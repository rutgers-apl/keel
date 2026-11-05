import Vbcf.Defs

/-!
# Vbcf core: the pool, interning, and node builders

`ck_intern` is the only way a node enters the pool; it is `Bcf.pushNode`.
A builder writes the candidate node at the tail of the pool (`st->plen`),
then `ck_intern` type-checks it (`ck_tyck`, which is `Op.resultTy` plus the
encoding constraints of `decodeNode`) and either returns the id of an equal
existing node or commits the candidate.

Rules never hold a raw pointer into the pool across a call that can grow it;
they index through `st->pool` each time.
-/

namespace Vbcf
open EmbC

/-- `words_eq(a, b, n)`: are the `n` words at `a` and at `b` equal? -/
def wordsEq : Fn := c_fn% u32 words_eq(u32 *a, u32 *b, u32 n) {
  u32 i;
  while (i < n) {
    if (a[i] != b[i]) { return 0; }
    i = i + 1;
  }
  return 1;
}

/-- The type of a node, from its header (see `Vbcf/Defs.lean`). -/
def tyOf : Fn := c_fn% u32 ty_of(u32 hdr) {
  u32 code;
  code = hdr & 0xff;
  if ((code & 7) == 1) { return TY_BOOL; }
  if ((code & 7) == 2) { return TY_LIST | (((hdr >> 16) & 1) << 8) | ((hdr >> 8) & 0xff); }
  if (code == BV_EXTRACT) { return ((hdr >> 24) & 0xff) - ((hdr >> 16) & 0xff) + 1; }
  if (code == BV_FROM_BOOL) { return (hdr >> 8) & 0xff; }
  return (hdr >> 16) & 0xff;
}

/-- Make room for `n` more words at the tail of the pool.  The pool grows by a
quarter at a time: it is the largest allocation, so headroom is kept small.
The new capacity is paid for from the work budget and from the memory
budget. -/
def ckRoom : Fn := c_fn% u32 ck_room(struct ck *st, u32 n) {
  u32 *np; u32 ncap; u64 need;
  need = (u64)st->plen + (u64)n;
  if (need <= (u64)st->pcap) { return 1; }
  if (need > (u64)MAX_POOL) { st->err = ERR_LIMIT; return 0; }
  ncap = (u32)(need + need / 4ull);
  if (ncap < 1024) { ncap = 1024; }
  if (ncap > MAX_POOL) { ncap = MAX_POOL; }
  if (st->work < ncap) { st->err = ERR_LIMIT; return 0; }
  st->work = st->work - ncap;
  if (st->mem < ncap) { st->err = ERR_LIMIT; return 0; }
  st->mem = st->mem - ncap;
  np = kvrealloc(st->pool, array_size((u64)ncap, sizeof(u32)));
  if (np == NULL) { st->err = ERR_NOMEM; return 0; }
  st->pool = np;
  st->pcap = ncap;
  return 1;
}

/-- Spend one unit of the work budget; 0 if it is used up. -/
def tick : Fn := c_fn% u32 tick(struct ck *st) {
  if (st->work == 0) { st->err = ERR_LIMIT; return 0; }
  st->work = st->work - 1;
  return 1;
}

/-- Spend `k` units of the work budget; 0 if fewer are left. -/
def spend : Fn := c_fn% u32 spend(struct ck *st, u32 k) {
  if (st->work < k) { st->err = ERR_LIMIT; return 0; }
  st->work = st->work - k;
  return 1;
}

/-- Push one word on the scratch stack.  Costs one unit of work, and the new
capacity (from both budgets) when the stack grows. -/
def push : Fn := c_fn% u32 push(struct ck *st, u32 v) {
  u32 *ns; u32 ncap;
  if (st->work == 0) { st->err = ERR_LIMIT; return 0; }
  st->work = st->work - 1;
  if (st->sp == st->scap) {
    if (st->scap >= MAX_POOL) { st->err = ERR_LIMIT; return 0; }
    ncap = st->scap * 2;
    if (ncap == 0) { ncap = 256; }
    if (st->work < ncap) { st->err = ERR_LIMIT; return 0; }
    st->work = st->work - ncap;
    if (st->mem < ncap) { st->err = ERR_LIMIT; return 0; }
    st->mem = st->mem - ncap;
    ns = kvrealloc(st->stk, array_size((u64)ncap, sizeof(u32)));
    if (ns == NULL) { st->err = ERR_NOMEM; return 0; }
    st->stk = ns;
    st->scap = ncap;
  }
  st->stk[st->sp] = v;
  st->sp = st->sp + 1;
  return 1;
}

/-- Do arguments `from..n` of the candidate node at `base` all have type `t`? -/
def ckAllTy : Fn := c_fn% u32 ck_all_ty(struct ck *st, u32 base, u32 n, u32 t) {
  u32 i; u32 ta;
  while (i < n) {
    ta = ty_of(st->pool[st->pool[base + 1 + i]]);
    if (ta != t) { return 0; }
    i = i + 1;
  }
  return 1;
}

/-- Sum of the widths of the bit-vector arguments, or `NOID` if one is not a bit-vector. -/
def ckSumBv : Fn := c_fn% u32 ck_sum_bv(struct ck *st, u32 base, u32 n) {
  u32 i; u32 t; u32 sum;
  while (i < n) {
    t = ty_of(st->pool[st->pool[base + 1 + i]]);
    if (t >= TY_BOOL) { return NOID; }
    sum = sum + t;
    i = i + 1;
  }
  return sum;
}

/-- Type-check the candidate node at the tail of the pool: `Op.resultTy`
together with the header constraints of `decodeNode`.  Returns 1 if well-typed. -/
def ckTyck : Fn := c_fn% u32 ck_tyck(struct ck *st) {
  u32 base; u32 hdr; u32 code; u32 n; u32 par; u32 lo; u32 hi;
  u32 t0; u32 t1; u32 t2; u32 r;
  base = st->plen;
  hdr = st->pool[base];
  code = hdr & 0xff;
  n = (hdr >> 8) & 0xff;
  par = hdr >> 16;
  lo = par & 0xff;
  hi = par >> 8;
  if (code == BV_VAR) { return n == 1 && hi == 0 && lo != 0; }
  if (code == BOOL_VAR) { return n == 1 && par == 0; }
  if (code == BOOL_VAL) { return n == 0 && (par & 0xfffe) == 0; }
  if (code == BV_VAL) {
    if (hi != 0 || lo == 0 || lo > 64 || n != (lo + 31) / 32) { return 0; }
    if (lo < 32) { return (st->pool[base + 1] >> lo) == 0; }
    if (lo > 32 && lo < 64) { return (st->pool[base + 2] >> (lo - 32)) == 0; }
    return 1;
  }
  if (n >= 1) { t0 = ty_of(st->pool[st->pool[base + 1]]); }
  if (n >= 2) { t1 = ty_of(st->pool[st->pool[base + 2]]); }
  if (n >= 3) { t2 = ty_of(st->pool[st->pool[base + 3]]); }
  if (code == BV_NEG || code == BV_NOT) { return n == 1 && hi == 0 && lo != 0 && t0 == lo; }
  if (code == BV_EXTRACT) { return n == 1 && t0 < TY_BOOL && lo <= hi && hi < t0; }
  if (code == BV_SEXT || code == BV_ZEXT) {
    return n == 1 && t0 < TY_BOOL && lo != 0 && t0 + hi == lo;
  }
  if (code == BV_SIZE) {
    if (n != 1 || hi != 0 || lo == 0 || t0 >= TY_BOOL) { return 0; }
    if (lo >= 9) { return 1; }
    return t0 < (1 << lo);
  }
  if (code == BV_REPEAT) { return n == 1 && t0 < TY_BOOL && lo != 0 && t0 * hi == lo; }
  if (code == BV_SUB || code == BV_SHL || code == BV_LSHR || code == BV_ASHR
      || code == BV_UDIV || code == BV_UREM || code == BV_SDIV || code == BV_SMOD) {
    return n == 2 && hi == 0 && lo != 0 && t0 == lo && t1 == lo;
  }
  if (code == BV_ITE) {
    return n == 3 && hi == 0 && lo != 0 && (t0 == TY_BOOL || t0 == 1) && t1 == lo && t2 == lo;
  }
  if (code == BV_ADD || code == BV_MUL || code == BV_OR || code == BV_AND || code == BV_XOR) {
    if (n < 2 || hi != 0 || lo == 0) { return 0; }
    r = ck_all_ty(st, base, n, lo);
    return r;
  }
  if (code == BV_CONCAT) {
    if (n < 2 || hi != 0 || lo == 0) { return 0; }
    r = ck_sum_bv(st, base, n);
    return r == lo;
  }
  if (code == BV_FROM_BOOL) {
    if (n < 1 || par != 0) { return 0; }
    r = ck_all_ty(st, base, n, TY_BOOL);
    return r;
  }
  if (code == BOOL_NOT) { return par == 0 && n == 1 && t0 == TY_BOOL; }
  if (code == BOOL_BITOF) { return hi == 0 && n == 1 && t0 < TY_BOOL && lo < t0; }
  if (code == BOOL_EQ || code == BOOL_DISTINCT) {
    return par == 0 && n == 2 && t0 == t1 && t0 < TY_LIST;
  }
  if (code == BOOL_UGT || code == BOOL_UGE || code == BOOL_SGT || code == BOOL_SGE
      || code == BOOL_ULT || code == BOOL_ULE || code == BOOL_SLT || code == BOOL_SLE) {
    return par == 0 && n == 2 && t0 < TY_BOOL && t0 == t1;
  }
  if (code == BOOL_IMPLIES) { return par == 0 && n == 2 && t0 == TY_BOOL && t1 == TY_BOOL; }
  if (code == BOOL_ITE) {
    return par == 0 && n == 3 && t0 == TY_BOOL && t1 == TY_BOOL && t2 == TY_BOOL;
  }
  if (code == BOOL_CONJ || code == BOOL_DISJ || code == BOOL_XOR) {
    if (par != 0 || n < 2) { return 0; }
    r = ck_all_ty(st, base, n, TY_BOOL);
    return r;
  }
  if (code == LIST_VAL) {
    if (hi != 0 || lo > 1) { return 0; }
    if (lo == 1) {
      r = ck_all_ty(st, base, n, TY_BOOL);
      return r;
    }
    r = ck_sum_bv(st, base, n);
    return r != NOID;
  }
  return 0;
}

/-- Hash of the `n` words at `off`. -/
def ckHash : Fn := c_fn% u32 ck_hash(struct ck *st, u32 off, u32 n) {
  u32 h; u32 i;
  h = 0x811c9dc5;
  while (i < n) {
    h = (h ^ st->pool[off + i]) * 0x01000193;
    i = i + 1;
  }
  h = h ^ (h >> 15);
  h = h * 0x2c1b3c6d;
  h = h ^ (h >> 12);
  return h;
}

/-- Enter node `id` in the hash table.  The table must have a free slot.
The node's size (it is hashed) and then each probe cost work; 0 if the
budget runs out, and then nothing is entered. -/
def ckHput : Fn := c_fn% u32 ck_hput(struct ck *st, u32 id) {
  u32 i; u32 mask; u32 h; u32 n;
  mask = st->hcap - 1;
  n = 1 + ((st->pool[id] >> 8) & 0xff);
  if (st->work < n) { st->err = ERR_LIMIT; return 0; }
  st->work = st->work - n;
  h = ck_hash(st, id, n);
  i = h & mask;
  while (st->htab[i] != 0) {
    if (st->work == 0) { st->err = ERR_LIMIT; return 0; }
    st->work = st->work - 1;
    i = (i + 1) & mask;
  }
  st->htab[i] = id + 1;
  st->hcnt = st->hcnt + 1;
  return 1;
}

/-- Double the hash table.  The new capacity is paid for from both budgets
(every node is hashed again, and `ck_hput` pays for that).  If the budget
runs out while the nodes are re-entered, the old table is put back, so on
failure the table is as before. -/
def ckHgrow : Fn := c_fn% u32 ck_hgrow(struct ck *st) {
  u32 *old; u32 *nt; u32 ocap; u32 ocnt; u32 i; u32 e; u32 ok;
  if (st->hcap >= MAX_POOL) { st->err = ERR_LIMIT; return 0; }
  if (st->work < st->hcap * 2) { st->err = ERR_LIMIT; return 0; }
  st->work = st->work - st->hcap * 2;
  if (st->mem < st->hcap * 2) { st->err = ERR_LIMIT; return 0; }
  st->mem = st->mem - st->hcap * 2;
  nt = kvcalloc((u64)st->hcap * 2ull, sizeof(u32));
  if (nt == NULL) { st->err = ERR_NOMEM; return 0; }
  old = st->htab;
  ocap = st->hcap;
  ocnt = st->hcnt;
  st->htab = nt;
  st->hcap = ocap * 2;
  st->hcnt = 0;
  while (i < ocap) {
    e = old[i];
    if (e != 0) {
      ok = ck_hput(st, e - 1);
      if (ok == 0) {
        st->hcap = ocap;
        st->hcnt = ocnt;
        st->htab = old;
        kvfree(nt);
        return 0;
      }
    }
    i = i + 1;
  }
  kvfree(old);
  return 1;
}

/-- `Bcf.pushNode` for the candidate node at the tail of the pool: its id if
an equal node exists, else commit it.  `NOID` if ill-typed or out of memory
or work.  The node's size is spent once it is type-checked (it is hashed)
and again for every probe (it is compared). -/
def ckIntern : Fn := c_fn% u32 ck_intern(struct ck *st) {
  u32 base; u32 n; u32 h; u32 i; u32 mask; u32 e; u32 ok;
  base = st->plen;
  ok = ck_tyck(st);
  if (ok == 0) { return NOID; }
  n = 1 + ((st->pool[base] >> 8) & 0xff);
  ok = spend(st, n);
  if (ok == 0) { return NOID; }
  if (((u64)st->hcnt + 1ull) * 2ull > (u64)st->hcap) {
    ok = ck_hgrow(st);
    if (ok == 0) { return NOID; }
  }
  mask = st->hcap - 1;
  h = ck_hash(st, base, n);
  i = h & mask;
  while (st->htab[i] != 0) {
    ok = spend(st, n);
    if (ok == 0) { return NOID; }
    e = st->htab[i] - 1;
    ok = words_eq(st->pool +> e, st->pool +> base, n);
    if (ok != 0) { return e; }
    i = (i + 1) & mask;
  }
  st->htab[i] = base + 1;
  st->hcnt = st->hcnt + 1;
  st->plen = base + n;
  return base;
}

/-! ## Builders.  `hdr` is `code | params << 16`; the builder adds the arity. -/

def mk0 : Fn := c_fn% u32 mk0(struct ck *st, u32 hdr) {
  u32 r;
  r = ck_room(st, 1);
  if (r == 0) { return NOID; }
  st->pool[st->plen] = hdr;
  r = ck_intern(st);
  return r;
}

def mk1 : Fn := c_fn% u32 mk1(struct ck *st, u32 hdr, u32 a) {
  u32 r;
  r = ck_room(st, 2);
  if (r == 0) { return NOID; }
  st->pool[st->plen] = hdr | (1 << 8);
  st->pool[st->plen + 1] = a;
  r = ck_intern(st);
  return r;
}

def mk2 : Fn := c_fn% u32 mk2(struct ck *st, u32 hdr, u32 a, u32 b) {
  u32 r;
  r = ck_room(st, 3);
  if (r == 0) { return NOID; }
  st->pool[st->plen] = hdr | (2 << 8);
  st->pool[st->plen + 1] = a;
  st->pool[st->plen + 2] = b;
  r = ck_intern(st);
  return r;
}

def mk3 : Fn := c_fn% u32 mk3(struct ck *st, u32 hdr, u32 a, u32 b, u32 c) {
  u32 r;
  r = ck_room(st, 4);
  if (r == 0) { return NOID; }
  st->pool[st->plen] = hdr | (3 << 8);
  st->pool[st->plen + 1] = a;
  st->pool[st->plen + 2] = b;
  st->pool[st->plen + 3] = c;
  r = ck_intern(st);
  return r;
}

/-- A node whose `n` arguments are `stk[base..base+n)`. -/
def mkn : Fn := c_fn% u32 mkn(struct ck *st, u32 hdr, u32 base, u32 n) {
  u32 r; u32 i;
  if (n > 255) { st->err = ERR_LIMIT; return NOID; }
  r = ck_room(st, 1 + n);
  if (r == 0) { return NOID; }
  st->pool[st->plen] = hdr | (n << 8);
  while (i < n) {
    st->pool[st->plen + 1 + i] = st->stk[base + i];
    i = i + 1;
  }
  r = ck_intern(st);
  return r;
}

/-- The bit-vector literal of width `w` and value `v` (`litOf (.bv w v)`). -/
def mkval : Fn := c_fn% u32 mkval(struct ck *st, u32 w, u64 v) {
  u32 r; u32 vlen;
  if (w == 0 || w > 64) { return NOID; }
  vlen = (w + 31) / 32;
  r = ck_room(st, 3);
  if (r == 0) { return NOID; }
  st->pool[st->plen] = BV_VAL | (vlen << 8) | (w << 16);
  st->pool[st->plen + 1] = (u32)v;
  if (vlen == 2) { st->pool[st->plen + 2] = (u32)(v >> 32ull); }
  r = ck_intern(st);
  return r;
}

def mkEq : Fn := c_fn% u32 mk_eq(struct ck *st, u32 a, u32 b) {
  u32 r;
  r = mk2(st, BOOL_EQ, a, b);
  return r;
}

def mkNot : Fn := c_fn% u32 mk_not(struct ck *st, u32 a) {
  u32 r;
  r = mk1(st, BOOL_NOT, a);
  return r;
}

/-- `Bcf.findNode st ⟨.boolNot, #[a]⟩`: the id of `not a` if it is already in
the pool, else `NOID`.  Never adds a node.  Each probe costs one unit of
work; if the budget runs out the result is `NOID` and `st->err` is set, so
the caller must check `st->err`. -/
def findNot : Fn := c_fn% u32 find_not(struct ck *st, u32 a) {
  u32 h; u32 i; u32 mask; u32 e; u32 ok;
  h = 0x811c9dc5;
  h = (h ^ (BOOL_NOT | (1 << 8))) * 0x01000193;
  h = (h ^ a) * 0x01000193;
  h = h ^ (h >> 15);
  h = h * 0x2c1b3c6d;
  h = h ^ (h >> 12);
  mask = st->hcap - 1;
  i = h & mask;
  while (st->htab[i] != 0) {
    ok = tick(st);
    if (ok == 0) { return NOID; }
    e = st->htab[i] - 1;
    if (st->pool[e] == (BOOL_NOT | (1 << 8)) && st->pool[e + 1] == a) { return e; }
    i = (i + 1) & mask;
  }
  return NOID;
}

/-- Push the arguments of node `id` on the scratch stack; returns 0 on failure. -/
def pushArgs : Fn := c_fn% u32 push_args(struct ck *st, u32 id) {
  u32 n; u32 i; u32 ok;
  n = (st->pool[id] >> 8) & 0xff;
  while (i < n) {
    ok = push(st, st->pool[id + 1 + i]);
    if (ok == 0) { return 0; }
    i = i + 1;
  }
  return 1;
}

/-- `ei`: the canonical id of the input expression at position `p`, or `NOID`. -/
def exprAt : Fn := c_fn% u32 expr_at(struct ck *st, u32 p) {
  u32 v;
  if (p >= st->nexpr) { return NOID; }
  v = st->proof[3 + p];
  if (v == 0) { return NOID; }
  return v - 1;
}

def coreFns : List Fn :=
  [wordsEq, tyOf, ckRoom, tick, spend, push, ckAllTy, ckSumBv, ckTyck, ckHash, ckHput, ckHgrow, ckIntern,
   mk0, mk1, mk2, mk3, mkn, mkval, mkEq, mkNot, findNot, pushArgs, exprAt]

end Vbcf
