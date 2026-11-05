import Vbcf.Rules.Basic

/-!
# Vbcf rules: constant evaluation, EVALUATE and DISTINCT_VALUES

`cval` is `Bcf.cval` (equivalently `memoVal`) restricted to values of at
most 64 bits.  Its result says what kind of value was found:

* `0` — the node is not constant (the Lean function returns `none`);
* `1..64` — a bit-vector of that width, value in `st->val`;
* `CV_BOOL` — a boolean, 0 or 1 in `st->val`;
* `NOID` — the C checker cannot evaluate this node (a value wider than 64
  bits, a list, nesting deeper than `MAX_DEPTH`, or the step's work budget
  is used up).  The caller must then
  reject the step; it must not treat the node as "not constant".

Like the Lean function, it evaluates *every* argument, including the branch
of an if-then-else that is not taken: a non-constant argument makes the whole
node non-constant.
-/

namespace Vbcf
open EmbC

c_const% CV_BOOL := 100

/-- The low `w` bits set, `1 ≤ w ≤ 64`. -/
def mask64 : Fn := c_fn% u64 mask64(u32 w) {
  if (w >= 64) { return 0xffffffffffffffffull; }
  return (1ull << (u64)w) - 1ull;
}

/-- `BitVec.smtUDiv` on `w`-bit values. -/
def udivW : Fn := c_fn% u64 udiv_w(u64 x, u64 y, u64 m) {
  if (y == 0ull) { return m; }
  return x / y;
}

/-- `BitVec.umod`. -/
def umodW : Fn := c_fn% u64 umod_w(u64 x, u64 y) {
  if (y == 0ull) { return x; }
  return x % y;
}

/-- `BitVec.smtSDiv` on `w`-bit values with mask `m`. -/
def sdivW : Fn := c_fn% u64 sdiv_w(u64 x, u64 y, u32 w, u64 m) {
  u64 sx; u64 sy; u64 r;
  sx = (x >> (u64)(w - 1)) & 1ull;
  sy = (y >> (u64)(w - 1)) & 1ull;
  if (sx == 0ull && sy == 0ull) {
    r = udiv_w(x, y, m);
    return r;
  }
  if (sx == 0ull) {
    r = udiv_w(x, (0ull - y) & m, m);
    return (0ull - r) & m;
  }
  if (sy == 0ull) {
    r = udiv_w((0ull - x) & m, y, m);
    return (0ull - r) & m;
  }
  r = udiv_w((0ull - x) & m, (0ull - y) & m, m);
  return r;
}

/-- `BitVec.smod` on `w`-bit values with mask `m`. -/
def smodW : Fn := c_fn% u64 smod_w(u64 x, u64 y, u32 w, u64 m) {
  u64 sx; u64 sy; u64 u;
  sx = (x >> (u64)(w - 1)) & 1ull;
  sy = (y >> (u64)(w - 1)) & 1ull;
  if (sx == 0ull && sy == 0ull) {
    u = umod_w(x, y);
    return u;
  }
  if (sx == 0ull) {
    u = umod_w(x, (0ull - y) & m);
    if (u == 0ull) { return u; }
    return (u + y) & m;
  }
  if (sy == 0ull) {
    u = umod_w((0ull - x) & m, y);
    if (u == 0ull) { return u; }
    return (y - u) & m;
  }
  u = umod_w((0ull - x) & m, (0ull - y) & m);
  return (0ull - u) & m;
}

def cval : Fn := c_fn% u32 cval(struct ck *st, u32 id, u32 depth) {
  u32 hdr; u32 code; u32 n; u32 par; u32 lo; u32 hi; u32 w; u32 cw; u32 i;
  u64 x; u64 y; u64 z; u64 m; u64 sb; u64 acc;
  if (depth == 0) { return NOID; }
  cw = tick(st);
  if (cw == 0) { return NOID; }
  hdr = st->pool[id];
  code = hdr & 0xff;
  n = (hdr >> 8) & 0xff;
  par = hdr >> 16;
  lo = par & 0xff;
  hi = par >> 8;
  if (code == BV_VAR || code == BOOL_VAR) { return 0; }
  if (code == BOOL_VAL) {
    st->val = (u64)(par & 1);
    return CV_BOOL;
  }
  if (code == BV_VAL) {
    x = (u64)st->pool[id + 1];
    if (n == 2) { x = x | ((u64)st->pool[id + 2] << 32ull); }
    st->val = x;
    return lo;
  }
  if (code == LIST_VAL) { return NOID; }
  w = ty_of(hdr);
  if (w < TY_BOOL && w > 64) { return NOID; }
  if (w == TY_BOOL) { w = CV_BOOL; }
  m = 1ull;
  if (w <= 64) { m = mask64(w); }
  if (code == BV_SIZE) {
    cw = ty_of(st->pool[st->pool[id + 1]]);
    st->val = (u64)cw;
    return w;
  }
  if (code == BV_NEG || code == BV_NOT || code == BV_EXTRACT || code == BV_SEXT
      || code == BV_ZEXT || code == BV_REPEAT || code == BOOL_NOT || code == BOOL_BITOF) {
    cw = cval(st, st->pool[id + 1], depth - 1);
    if (cw == 0 || cw == NOID) { return cw; }
    x = st->val;
    if (code == BV_NEG) { x = (0ull - x) & m; }
    else if (code == BV_NOT) { x = (~x) & m; }
    else if (code == BV_EXTRACT) { x = (x >> (u64)lo) & m; }
    else if (code == BV_SEXT) {
      if (((x >> (u64)(cw - 1)) & 1ull) != 0ull) {
        y = mask64(cw);
        x = x | (m & ~y);
      }
    }
    else if (code == BV_REPEAT) {
      if (cw < 64) {
        y = 0ull;
        while (i < hi) {
          y = (y << (u64)cw) | x;
          i = i + 1;
        }
        x = y;
      }
    }
    else if (code == BOOL_NOT) { x = 1ull - x; }
    else if (code == BOOL_BITOF) { x = (x >> (u64)lo) & 1ull; }
    st->val = x;
    return w;
  }
  if (code == BV_SUB || code == BV_SHL || code == BV_LSHR || code == BV_ASHR || code == BV_UDIV
      || code == BV_UREM || code == BV_SDIV || code == BV_SMOD || code == BOOL_EQ
      || code == BOOL_DISTINCT || code == BOOL_UGT || code == BOOL_UGE || code == BOOL_SGT
      || code == BOOL_SGE || code == BOOL_ULT || code == BOOL_ULE || code == BOOL_SLT
      || code == BOOL_SLE || code == BOOL_IMPLIES) {
    cw = cval(st, st->pool[id + 1], depth - 1);
    if (cw == 0 || cw == NOID) { return cw; }
    x = st->val;
    cw = cval(st, st->pool[id + 2], depth - 1);
    if (cw == 0 || cw == NOID) { return cw; }
    y = st->val;
    if (code == BV_SUB) { z = (x - y) & m; }
    else if (code == BV_SHL) {
      z = 0ull;
      if (y < (u64)w) { z = (x << y) & m; }
    }
    else if (code == BV_LSHR) {
      z = 0ull;
      if (y < (u64)w) { z = x >> y; }
    }
    else if (code == BV_ASHR) {
      sb = (x >> (u64)(w - 1)) & 1ull;
      if (y >= (u64)w) {
        z = 0ull;
        if (sb != 0ull) { z = m; }
      } else {
        z = x >> y;
        if (sb != 0ull) { z = z | (m & ~(m >> y)); }
      }
    }
    else if (code == BV_UDIV) { z = udiv_w(x, y, m); }
    else if (code == BV_UREM) { z = umod_w(x, y); }
    else if (code == BV_SDIV) { z = sdiv_w(x, y, w, m); }
    else if (code == BV_SMOD) { z = smod_w(x, y, w, m); }
    else if (code == BOOL_EQ) { z = (u64)(x == y); }
    else if (code == BOOL_DISTINCT) { z = (u64)(x != y); }
    else if (code == BOOL_IMPLIES) { z = (1ull - x) | y; }
    else if (code == BOOL_ULT) { z = (u64)(x < y); }
    else if (code == BOOL_ULE) { z = (u64)(x <= y); }
    else if (code == BOOL_UGT) { z = (u64)(y < x); }
    else if (code == BOOL_UGE) { z = (u64)(y <= x); }
    else {
      sb = 1ull << (u64)(cw - 1);
      x = x ^ sb;
      y = y ^ sb;
      if (code == BOOL_SLT) { z = (u64)(x < y); }
      else if (code == BOOL_SLE) { z = (u64)(x <= y); }
      else if (code == BOOL_SGT) { z = (u64)(y < x); }
      else { z = (u64)(y <= x); }
    }
    st->val = z;
    return w;
  }
  if (code == BV_ITE || code == BOOL_ITE) {
    cw = cval(st, st->pool[id + 1], depth - 1);
    if (cw == 0 || cw == NOID) { return cw; }
    x = st->val;
    cw = cval(st, st->pool[id + 2], depth - 1);
    if (cw == 0 || cw == NOID) { return cw; }
    y = st->val;
    cw = cval(st, st->pool[id + 3], depth - 1);
    if (cw == 0 || cw == NOID) { return cw; }
    z = st->val;
    if (x != 0ull) { z = y; }
    st->val = z;
    return w;
  }
  if (code == BV_ADD || code == BV_MUL || code == BV_OR || code == BV_AND || code == BV_XOR
      || code == BV_CONCAT || code == BV_FROM_BOOL || code == BOOL_CONJ || code == BOOL_DISJ
      || code == BOOL_XOR) {
    acc = 0ull;
    if (code == BV_MUL || code == BOOL_CONJ) { acc = 1ull; }
    if (code == BV_AND) { acc = m; }
    while (i < n) {
      cw = cval(st, st->pool[id + 1 + i], depth - 1);
      if (cw == 0 || cw == NOID) { return cw; }
      x = st->val;
      if (code == BV_ADD) { acc = (acc + x) & m; }
      else if (code == BV_MUL) { acc = (acc * x) & m; }
      else if (code == BV_OR || code == BOOL_DISJ) { acc = acc | x; }
      else if (code == BV_AND || code == BOOL_CONJ) { acc = acc & x; }
      else if (code == BV_XOR || code == BOOL_XOR) { acc = acc ^ x; }
      else if (code == BV_CONCAT) { acc = (acc << (u64)cw) | x; }
      else { acc = acc | (x << (u64)i); }
      i = i + 1;
    }
    st->val = acc;
    return w;
  }
  return NOID;
}

def rEvaluate : Fn := c_fn% u32 r_evaluate(struct ck *st, u32 np, u32 na) {
  u32 e; u32 w; u32 lit; u32 r;
  if (np != 0 || na != 1) { return NOID; }
  e = expr_at(st, st->par[0]);
  if (e == NOID) { return NOID; }
  w = cval(st, e, MAX_DEPTH);
  if (w == 0 || w == NOID) { return NOID; }
  if (w == CV_BOOL) {
    lit = mk0(st, BOOL_VAL | ((u32)st->val << 16));
  } else {
    lit = mkval(st, w, st->val);
  }
  if (lit == NOID) { return NOID; }
  r = mk_eq(st, e, lit);
  return r;
}

def rDistinctValues : Fn := c_fn% u32 r_distinct_values(struct ck *st, u32 np, u32 na) {
  u32 a; u32 b; u32 code; u32 r;
  if (np != 0 || na != 2) { return NOID; }
  a = expr_at(st, st->par[0]);
  if (a == NOID) { return NOID; }
  b = expr_at(st, st->par[1]);
  if (b == NOID) { return NOID; }
  code = st->pool[a] & 0xff;
  if (code != BV_VAL && code != BOOL_VAL) { return NOID; }
  if ((st->pool[b] & 0xff) != code) { return NOID; }
  if (code == BV_VAL && ((st->pool[a] >> 16) != (st->pool[b] >> 16))) { return NOID; }
  if (a == b) { return NOID; }
  r = mk_eq(st, a, b);
  if (r == NOID) { return NOID; }
  r = mk_not(st, r);
  return r;
}

def evalFns : List Fn :=
  [mask64, udivW, umodW, sdivW, smodW, cval, rEvaluate, rDistinctValues]

end Vbcf
