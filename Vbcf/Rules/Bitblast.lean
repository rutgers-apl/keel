import Vbcf.Rules.Basic

/-!
# Vbcf rules: BITBLAST

`r_bitblast` is `Bcf.ruleBitblast` (`Bcf/Check.lean`); the helpers mirror the
executable definitions of `Bcf/Bitblast.lean`.  The rule only *inspects* the
pool: no function in this file creates a node.

## Representation of the Lean lists

* `bitsOf st i` is the argument words of the `from_bool` node `i`.  Helpers
  whose lists are exactly such argument lists take the node id and read the
  words in place (`bb_var`, `bb_val`, `bb_ite`, `bb_bitwise`, `bb_concat`,
  `bb_extract`, `bb_sext`, `bb_eq_bits`).
* Every other list of bit ids is a range `stk[base..base+n)` of the scratch
  stack, least significant bit first, passed as `(base, n)`.  A helper that
  returns `Option (List Nat)` pushes the list and returns its base, or `NOID`
  for `none`; the length is always that of its input list.
* A reversed list is never built: `bb_ult` and `bb_slt` walk their ranges
  from the top.

Lean's `args.toList` of a node is its argument words, except for the leaves
`BV_VAL`, `BV_VAR` and `BOOL_VAR`, whose words are not children and whose Lean
argument list is empty (`bb_nargs`).  A header is always compared before the
argument words behind it are read.
-/

namespace Vbcf
open EmbC

/-! Headers (`code | arity << 8`, no parameters) of the circuit nodes. -/
c_const% BB_NOT1 := 0x181
c_const% BB_EQ2 := 0x211
c_const% BB_XOR2 := 0x239
c_const% BB_CONJ2 := 0x201
c_const% BB_DISJ2 := 0x241
c_const% BB_ITE3 := 0x329

/-- `args.size` of the Lean node `id`: the leaves that carry a value or an
identity word have no arguments. -/
def bbNargs : Fn := c_fn% u32 bb_nargs(struct ck *st, u32 id) {
  u32 code;
  code = st->pool[id] & 0xff;
  if (code == BV_VAL || code == BV_VAR || code == BOOL_VAR) { return 0; }
  return (st->pool[id] >> 8) & 0xff;
}

/-- `isNode st i ⟨op, #[a]⟩`, where `hdr` is the header of a one-argument `op`
(`isNotOf` with `BB_NOT1`). -/
def bbIs1 : Fn := c_fn% u32 bb_is1(struct ck *st, u32 i, u32 hdr, u32 a) {
  if (st->pool[i] != hdr) { return 0; }
  return st->pool[i + 1] == a;
}

/-- `isNode st i ⟨op, #[a, b]⟩`, where `hdr` is the header of a two-argument
`op` (`isEqOf`, `isXorOf`, `isConjOf` with `BB_EQ2`, `BB_XOR2`, `BB_CONJ2`). -/
def bbIs2 : Fn := c_fn% u32 bb_is2(struct ck *st, u32 i, u32 hdr, u32 a, u32 b) {
  if (st->pool[i] != hdr) { return 0; }
  return st->pool[i + 1] == a && st->pool[i + 2] == b;
}

/-- `bbVar st a bs`, `bs` the bits of the `from_bool` node `b`. -/
def bbVar : Fn := c_fn% u32 bb_var(struct ck *st, u32 a, u32 b) {
  u32 n; u32 i; u32 ok;
  n = (st->pool[b] >> 8) & 0xff;
  while (i < n) {
    ok = bb_is1(st, st->pool[b + 1 + i], BOOL_BITOF | (1 << 8) | (i << 16), a);
    if (ok == 0) { return 0; }
    i = i + 1;
  }
  return 1;
}

/-- `bbVal bi v bs`, `v` the value of the `BV_VAL` node `a`, `bs` the bits of
the `from_bool` node `b`. -/
def bbVal : Fn := c_fn% u32 bb_val(struct ck *st, u32 a, u32 b) {
  u32 n; u32 vl; u32 i; u32 bit; u32 x;
  n = (st->pool[b] >> 8) & 0xff;
  vl = (st->pool[a] >> 8) & 0xff;
  while (i < n) {
    bit = 0;
    if (i < 32) {
      if (vl >= 1) { bit = (st->pool[a + 1] >> i) & 1; }
    } else if (i < 64) {
      if (vl >= 2) { bit = (st->pool[a + 2] >> (i - 32)) & 1; }
    }
    x = st->pool[b + 1 + i];
    if (bit != 0) {
      if (x != st->tt) { return 0; }
    } else {
      if (x != st->ff) { return 0; }
    }
    i = i + 1;
  }
  return 1;
}

/-- `bbIteBit st c t e b`. -/
def bbIteBit : Fn := c_fn% u32 bb_ite_bit(struct ck *st, u32 c, u32 t, u32 e, u32 b) {
  u32 d1; u32 d2; u32 ok;
  if (st->pool[b] != BB_CONJ2) { return 0; }
  d1 = st->pool[b + 1];
  d2 = st->pool[b + 2];
  ok = bb_is2(st, d2, BB_DISJ2, c, e);
  if (ok == 0) { return 0; }
  if (st->pool[d1] != BB_DISJ2) { return 0; }
  ok = bb_is1(st, st->pool[d1 + 1], BB_NOT1, c);
  if (ok == 0) { return 0; }
  return st->pool[d1 + 2] == t;
}

/-- `bbIte st c ts es bs`, with `ts`, `es`, `bs` the bits of the `from_bool`
nodes `t`, `e`, `b`. -/
def bbIte : Fn := c_fn% u32 bb_ite(struct ck *st, u32 c, u32 t, u32 e, u32 b) {
  u32 n; u32 nt; u32 ne; u32 i; u32 ok;
  n = (st->pool[b] >> 8) & 0xff;
  nt = (st->pool[t] >> 8) & 0xff;
  ne = (st->pool[e] >> 8) & 0xff;
  while (i < n) {
    if (i >= nt || i >= ne) { return 0; }
    ok = bb_ite_bit(st, c, st->pool[t + 1 + i], st->pool[e + 1 + i], st->pool[b + 1 + i]);
    if (ok == 0) { return 0; }
    i = i + 1;
  }
  return 1;
}

/-- `zipAll (fun p x => isNotOf st p x) ps xs` for the stack ranges
`ps = stk[pb..pb+np)`, `xs = stk[xb..xb+nx)`. -/
def bbZipNot : Fn := c_fn% u32 bb_zip_not(struct ck *st, u32 pb, u32 np, u32 xb, u32 nx) {
  u32 i; u32 ok;
  if (np != nx) { return 0; }
  while (i < np) {
    ok = bb_is1(st, st->stk[pb + i], BB_NOT1, st->stk[xb + i]);
    if (ok == 0) { return 0; }
    i = i + 1;
  }
  return 1;
}

/-- Is the stack range `stk[pb..pb+np)` equal to the list `stk[xb..xb+nx)`? -/
def bbListEq : Fn := c_fn% u32 bb_list_eq(struct ck *st, u32 pb, u32 np, u32 xb, u32 nx) {
  u32 i;
  if (np != nx) { return 0; }
  while (i < np) {
    if (st->stk[pb + i] != st->stk[xb + i]) { return 0; }
    i = i + 1;
  }
  return 1;
}

/-- `preSum st rs` (`k = 0`) and `preAdder st rs` (`k = 1`) for
`rs = stk[rb..rb+n)`: for each `r`, argument `k` of the first argument of `r`.
Pushes the `n` results and returns their base, or `NOID` for `none`. -/
def bbPre : Fn := c_fn% u32 bb_pre(struct ck *st, u32 rb, u32 n, u32 k) {
  u32 base; u32 i; u32 r; u32 s; u32 m; u32 ok;
  base = st->sp;
  while (i < n) {
    r = st->stk[rb + i];
    m = bb_nargs(st, r);
    if (m == 0) { return NOID; }
    s = st->pool[r + 1];
    m = bb_nargs(st, s);
    if (m <= k) { return NOID; }
    ok = push(st, st->pool[s + 1 + k]);
    if (ok == 0) { return NOID; }
    i = i + 1;
  }
  return base;
}

/-- `carryNode st pa pb pc c`. -/
def bbCarry : Fn := c_fn% u32 bb_carry(struct ck *st, u32 pa, u32 pb, u32 pc, u32 c) {
  u32 u; u32 v; u32 ok;
  if (st->pool[c] != BB_DISJ2) { return 0; }
  u = st->pool[c + 1];
  v = st->pool[c + 2];
  ok = bb_is2(st, u, BB_CONJ2, pa, pb);
  if (ok == 0) { return 0; }
  if (st->pool[v] != BB_CONJ2) { return 0; }
  ok = bb_is2(st, st->pool[v + 1], BB_XOR2, pa, pb);
  if (ok == 0) { return 0; }
  return st->pool[v + 2] == pc;
}

/-- `ripple st bi as bs rs init` (with its loop `rippleGo`) for the stack
ranges `as = stk[xb..xb+nx)`, `bs = stk[yb..yb+ny)`, `rs = stk[rb..rb+nr)`.
The three lists must be non-empty and equally long. -/
def bbRipple : Fn := c_fn% u32 bb_ripple(struct ck *st, u32 xb, u32 nx, u32 yb, u32 ny,
    u32 rb, u32 nr, u32 init) {
  u32 i; u32 a; u32 b; u32 r; u32 s; u32 c; u32 pa; u32 pb; u32 pc; u32 ok;
  if (nx == 0 || ny != nx || nr != nx) { return 0; }
  while (i < nx) {
    a = st->stk[xb + i];
    b = st->stk[yb + i];
    r = st->stk[rb + i];
    if (st->pool[r] != BB_XOR2) { return 0; }
    s = st->pool[r + 1];
    c = st->pool[r + 2];
    ok = bb_is2(st, s, BB_XOR2, a, b);
    if (ok == 0) { return 0; }
    if (i == 0) {
      if (init != 0) {
        if (c != st->tt) { return 0; }
      } else {
        if (c != st->ff) { return 0; }
      }
    } else {
      ok = bb_carry(st, pa, pb, pc, c);
      if (ok == 0) { return 0; }
    }
    pa = a;
    pb = b;
    pc = c;
    i = i + 1;
  }
  return 1;
}

/-- `bbAddRev st bi xss.reverse sum`, where `xss` are the bits of the
arguments of node `a` (all `from_bool` nodes) and `sum = stk[bsb..bsb+nb)`.
Operand `k` is pushed for its ripple check and popped again; the peeled
partial sums stay on the stack. -/
def bbAdd : Fn := c_fn% u32 bb_add(struct ck *st, u32 a, u32 bsb, u32 nb) {
  u32 n; u32 k; u32 x; u32 nx; u32 xb; u32 sb; u32 pre; u32 i; u32 ok;
  n = (st->pool[a] >> 8) & 0xff;
  if (n == 0) { return 0; }
  sb = bsb;
  k = n;
  while (k > 1) {
    k = k - 1;
    x = st->pool[a + 1 + k];
    nx = (st->pool[x] >> 8) & 0xff;
    pre = bb_pre(st, sb, nb, 0);
    if (pre == NOID) { return 0; }
    xb = st->sp;
    ok = push_args(st, x);
    if (ok == 0) { return 0; }
    ok = bb_ripple(st, pre, nb, xb, nx, sb, nb, 0);
    if (ok == 0) { return 0; }
    st->sp = xb;
    sb = pre;
  }
  x = st->pool[a + 1];
  nx = (st->pool[x] >> 8) & 0xff;
  if (nb != nx) { return 0; }
  while (i < nb) {
    if (st->stk[sb + i] != st->pool[x + 1 + i]) { return 0; }
    i = i + 1;
  }
  return 1;
}

/-- `bbNeg st bi xs bs` for `xs = stk[xb..xb+nx)`, `bs = stk[bsb..bsb+nb)`. -/
def bbNeg : Fn := c_fn% u32 bb_neg(struct ck *st, u32 xb, u32 nx, u32 bsb, u32 nb) {
  u32 pre; u32 adder; u32 i; u32 ok;
  pre = bb_pre(st, bsb, nb, 0);
  if (pre == NOID) { return 0; }
  adder = bb_pre(st, bsb, nb, 1);
  if (adder == NOID) { return 0; }
  ok = bb_zip_not(st, pre, nb, xb, nx);
  if (ok == 0) { return 0; }
  while (i < nb) {
    if (st->stk[adder + i] != st->ff) { return 0; }
    i = i + 1;
  }
  ok = bb_ripple(st, pre, nb, adder, nb, bsb, nb, 1);
  return ok;
}

/-- `bbSub st bi xs ys bs` for `xs = stk[xb..xb+nx)`, `ys = stk[yb..yb+ny)`,
`bs = stk[bsb..bsb+nb)`. -/
def bbSub : Fn := c_fn% u32 bb_sub(struct ck *st, u32 xb, u32 nx, u32 yb, u32 ny,
    u32 bsb, u32 nb) {
  u32 adder; u32 ok;
  adder = bb_pre(st, bsb, nb, 1);
  if (adder == NOID) { return 0; }
  ok = bb_zip_not(st, adder, nb, yb, ny);
  if (ok == 0) { return 0; }
  ok = bb_ripple(st, xb, nx, adder, nb, bsb, nb, 1);
  return ok;
}

/-- `bbBitwise st op xss 0 bs` (with `chainRev`), where `code` is the code of
`op`, `xss` the bits of the arguments of node `a` (all `from_bool` nodes) and
`bs` the bits of the `from_bool` node `b`. -/
def bbBitwise : Fn := c_fn% u32 bb_bitwise(struct ck *st, u32 code, u32 a, u32 b) {
  u32 n; u32 nb; u32 hdr; u32 i; u32 k; u32 x; u32 cur;
  n = (st->pool[a] >> 8) & 0xff;
  nb = (st->pool[b] >> 8) & 0xff;
  hdr = code | (2 << 8);
  while (i < nb) {
    k = 0;
    while (k < n) {
      x = st->pool[a + 1 + k];
      if (i >= ((st->pool[x] >> 8) & 0xff)) { return 0; }
      k = k + 1;
    }
    if (n == 0) { return 0; }
    cur = st->pool[b + 1 + i];
    k = n;
    while (k > 1) {
      k = k - 1;
      x = st->pool[a + 1 + k];
      if (st->pool[cur] != hdr) { return 0; }
      if (st->pool[cur + 2] != st->pool[x + 1 + i]) { return 0; }
      cur = st->pool[cur + 1];
    }
    x = st->pool[a + 1];
    if (cur != st->pool[x + 1 + i]) { return 0; }
    i = i + 1;
  }
  return 1;
}

/-- `bs == xss.reverse.flatten`, where `xss` are the bits of the arguments of
node `a` (all `from_bool` nodes) and `bs` the bits of the `from_bool` node `b`. -/
def bbConcat : Fn := c_fn% u32 bb_concat(struct ck *st, u32 a, u32 b) {
  u32 n; u32 nb; u32 k; u32 x; u32 nx; u32 j; u32 pos;
  n = (st->pool[a] >> 8) & 0xff;
  nb = (st->pool[b] >> 8) & 0xff;
  k = n;
  while (k > 0) {
    k = k - 1;
    x = st->pool[a + 1 + k];
    nx = (st->pool[x] >> 8) & 0xff;
    j = 0;
    while (j < nx) {
      if (pos >= nb) { return 0; }
      if (st->pool[b + 1 + pos] != st->pool[x + 1 + j]) { return 0; }
      pos = pos + 1;
      j = j + 1;
    }
  }
  return pos == nb;
}

/-- `bs == (xs.drop lo).take (hi - lo + 1)`, with `xs`, `bs` the bits of the
`from_bool` nodes `x`, `b`.  The subtractions truncate at 0 as in Lean. -/
def bbExtract : Fn := c_fn% u32 bb_extract(struct ck *st, u32 hi, u32 lo, u32 x, u32 b) {
  u32 nx; u32 nb; u32 cnt; u32 avail; u32 i;
  nx = (st->pool[x] >> 8) & 0xff;
  nb = (st->pool[b] >> 8) & 0xff;
  cnt = 1;
  if (hi > lo) { cnt = hi - lo + 1; }
  if (nx > lo) { avail = nx - lo; }
  if (cnt > avail) { cnt = avail; }
  if (nb != cnt) { return 0; }
  while (i < nb) {
    if (st->pool[b + 1 + i] != st->pool[x + 1 + lo + i]) { return 0; }
    i = i + 1;
  }
  return 1;
}

/-- `bbSext xs bs e`, with `xs`, `bs` the bits of the `from_bool` nodes `x`, `b`. -/
def bbSext : Fn := c_fn% u32 bb_sext(struct ck *st, u32 x, u32 b, u32 e) {
  u32 nx; u32 nb; u32 i;
  nx = (st->pool[x] >> 8) & 0xff;
  nb = (st->pool[b] >> 8) & 0xff;
  if (nx == 0) { return 0; }
  if (nb != nx + e) { return 0; }
  while (i < nb) {
    if (i < nx) {
      if (st->pool[b + 1 + i] != st->pool[x + 1 + i]) { return 0; }
    } else {
      if (st->pool[b + 1 + i] != st->pool[x + nx]) { return 0; }
    }
    i = i + 1;
  }
  return 1;
}

/-- `ultBase st l0 r0 res`. -/
def bbUltBase : Fn := c_fn% u32 bb_ult_base(struct ck *st, u32 l0, u32 r0, u32 res) {
  u32 ok;
  if (st->pool[res] != BB_CONJ2) { return 0; }
  if (st->pool[res + 2] != r0) { return 0; }
  ok = bb_is1(st, st->pool[res + 1], BB_NOT1, l0);
  return ok;
}

/-- `ultGo st withEq ls.reverse rs.reverse res` for the stack ranges
`ls = stk[lb..lb+nl)`, `rs = stk[rb..rb+nr)` (least significant bit first; the
walk starts at the top).  The lists must be non-empty and equally long. -/
def bbUlt : Fn := c_fn% u32 bb_ult(struct ck *st, u32 weq, u32 lb, u32 nl, u32 rb, u32 nr,
    u32 res) {
  u32 i; u32 l; u32 r; u32 cur; u32 cl; u32 cr; u32 ok;
  if (nl == 0 || nl != nr) { return 0; }
  cur = res;
  i = nl;
  while (i > 1) {
    i = i - 1;
    l = st->stk[lb + i];
    r = st->stk[rb + i];
    if (st->pool[cur] != BB_DISJ2) { return 0; }
    cl = st->pool[cur + 1];
    cr = st->pool[cur + 2];
    if (st->pool[cl] != BB_CONJ2) { return 0; }
    ok = bb_is2(st, st->pool[cl + 1], BB_EQ2, l, r);
    if (ok == 0) { return 0; }
    if (st->pool[cr] != BB_CONJ2) { return 0; }
    ok = bb_is1(st, st->pool[cr + 1], BB_NOT1, l);
    if (ok == 0) { return 0; }
    if (st->pool[cr + 2] != r) { return 0; }
    cur = st->pool[cl + 2];
  }
  l = st->stk[lb];
  r = st->stk[rb];
  if (weq != 0) {
    if (st->pool[cur] != BB_DISJ2) { return 0; }
    ok = bb_is2(st, st->pool[cur + 2], BB_EQ2, l, r);
    if (ok == 0) { return 0; }
    cur = st->pool[cur + 1];
  }
  ok = bb_ult_base(st, l, r, cur);
  return ok;
}

/-- `sltChain st withEq ls.reverse rs.reverse res` for the stack ranges
`ls = stk[lb..lb+nl)`, `rs = stk[rb..rb+nr)`. -/
def bbSlt : Fn := c_fn% u32 bb_slt(struct ck *st, u32 weq, u32 lb, u32 nl, u32 rb, u32 nr,
    u32 res) {
  u32 ls; u32 rs; u32 s; u32 n; u32 ok;
  if (nl == 0 || nr == 0) { return 0; }
  if (nl < 2) { return 0; }
  ls = st->stk[lb + nl - 1];
  rs = st->stk[rb + nr - 1];
  if (st->pool[res] != BB_DISJ2) { return 0; }
  s = st->pool[res + 1];
  n = st->pool[res + 2];
  if (st->pool[n] != BB_CONJ2) { return 0; }
  if (st->pool[n + 1] != ls) { return 0; }
  ok = bb_is1(st, st->pool[n + 2], BB_NOT1, rs);
  if (ok == 0) { return 0; }
  if (st->pool[s] != BB_CONJ2) { return 0; }
  ok = bb_is2(st, st->pool[s + 1], BB_EQ2, ls, rs);
  if (ok == 0) { return 0; }
  ok = bb_ult(st, weq, lb, nl - 1, rb, nr - 1, st->pool[s + 2]);
  return ok;
}

/-- The fill test `isFill f` of a shift: `isFalseNode st f` if `arith == 0`,
else `isLastOf xs f` for `xs = stk[xb..xb+nx)`. -/
def bbIsFill : Fn := c_fn% u32 bb_is_fill(struct ck *st, u32 arith, u32 xb, u32 nx, u32 f) {
  if (arith == 0) { return st->pool[f] == HDR_FALSE; }
  if (nx == 0) { return 0; }
  return st->stk[xb + nx - 1] == f;
}

/-- `bbShiftLimit st cond isFill bs` for `bs = stk[bsb..bsb+nb)`; `isFill` is
given by `arith`, `xb`, `nx` as in `bb_is_fill`.  Pushes the guarded vector
and returns its base, or `NOID` for `none`. -/
def bbShiftLimit : Fn := c_fn% u32 bb_shift_limit(struct ck *st, u32 cond, u32 arith,
    u32 xb, u32 nx, u32 bsb, u32 nb) {
  u32 base; u32 i; u32 b; u32 ok;
  base = st->sp;
  while (i < nb) {
    b = st->stk[bsb + i];
    if (st->pool[b] != BB_ITE3) { return NOID; }
    if (st->pool[b + 1] != cond) { return NOID; }
    ok = bb_is_fill(st, arith, xb, nx, st->pool[b + 3]);
    if (ok == 0) { return NOID; }
    ok = push(st, st->pool[b + 2]);
    if (ok == 0) { return NOID; }
    i = i + 1;
  }
  return base;
}

/-- `bbLog2 n`: the least `k` with `n ≤ 2^k`.  (`k` stops at 31; `n` is a
list length, at most 255.) -/
def bbLog2 : Fn := c_fn% u32 bb_log2(u32 n) {
  u32 k;
  while (k < 31 && (1 << k) < n) { k = k + 1; }
  return k;
}

/-- `bbLshStage st b t res` for `res = stk[rb..rb+n)`.  Pushes `pre` and
returns its base, or `NOID` for `none`. -/
def bbLshStage : Fn := c_fn% u32 bb_lsh_stage(struct ck *st, u32 b, u32 t, u32 rb, u32 n) {
  u32 base; u32 j; u32 r; u32 inj; u32 ok;
  base = st->sp;
  while (j < n) {
    r = st->stk[rb + j];
    if (st->pool[r] != BB_ITE3) { return NOID; }
    ok = push(st, st->pool[r + 3]);
    if (ok == 0) { return NOID; }
    j = j + 1;
  }
  j = 0;
  while (j < n) {
    r = st->stk[rb + j];
    if (st->pool[r + 1] != b) { return NOID; }
    inj = st->pool[r + 2];
    if (j < t) {
      if (st->pool[inj] != HDR_FALSE) { return NOID; }
    } else {
      if (st->stk[base + (j - t)] != inj) { return NOID; }
    }
    j = j + 1;
  }
  return base;
}

/-- `bbRshStage st isFill b t res` for `res = stk[rb..rb+n)`; `isFill` is
given by `arith`, `xb`, `nx` as in `bb_is_fill`.  Pushes `pre` and returns its
base, or `NOID` for `none`. -/
def bbRshStage : Fn := c_fn% u32 bb_rsh_stage(struct ck *st, u32 arith, u32 xb, u32 nx,
    u32 b, u32 t, u32 rb, u32 n) {
  u32 base; u32 j; u32 r; u32 ok;
  base = st->sp;
  while (j < n) {
    r = st->stk[rb + j];
    if (st->pool[r] != BB_ITE3) { return NOID; }
    if (j + t >= n) {
      ok = push(st, st->pool[r + 3]);
    } else {
      ok = push(st, st->pool[r + 2]);
    }
    if (ok == 0) { return NOID; }
    j = j + 1;
  }
  j = 0;
  while (j < n) {
    r = st->stk[rb + j];
    if (j + t >= n) {
      if (st->pool[r + 1] != b) { return NOID; }
      ok = bb_is_fill(st, arith, xb, nx, st->pool[r + 2]);
      if (ok == 0) { return NOID; }
    } else {
      ok = bb_is1(st, st->pool[r + 1], BB_NOT1, b);
      if (ok == 0) { return NOID; }
      if (st->stk[base + j + t] != st->pool[r + 3]) { return NOID; }
    }
    j = j + 1;
  }
  return base;
}

/-- `bbShift st bi isFill stage xs ys bs` (with `bbWidthBits` and `bbStages`)
for `xs = stk[xb..xb+nx)`, `ys = stk[yb..yb+ny)`, `bs = stk[bsb..bsb+nb)`.
`kind` selects the instance used by `bbTerm`: 0 is `bvShl` (`isFalseNode`,
`bbLshStage`), 1 is `bvLshr` (`isFalseNode`, `bbRshStage`), 2 is `bvAshr`
(`isLastOf xs`, `bbRshStage`). -/
def bbShift : Fn := c_fn% u32 bb_shift(struct ck *st, u32 kind, u32 xb, u32 nx, u32 yb, u32 ny,
    u32 bsb, u32 nb) {
  u32 arith; u32 b0; u32 cond; u32 wb; u32 i; u32 bit; u32 res; u32 ok;
  if (kind == 2) { arith = 1; }
  if (nb == 0) { return 0; }
  b0 = st->stk[bsb];
  if (st->pool[b0] != BB_ITE3) { return 0; }
  cond = st->pool[b0 + 1];
  wb = st->sp;
  while (i < ny) {
    bit = 0;
    if (i < 32) { bit = (nx >> i) & 1; }
    if (bit != 0) {
      ok = push(st, st->tt);
    } else {
      ok = push(st, st->ff);
    }
    if (ok == 0) { return 0; }
    i = i + 1;
  }
  ok = bb_ult(st, 0, yb, ny, wb, ny, cond);
  if (ok == 0) { return 0; }
  res = bb_shift_limit(st, cond, arith, xb, nx, bsb, nb);
  if (res == NOID) { return 0; }
  i = bb_log2(nx);
  while (i > 0) {
    i = i - 1;
    if (i >= ny) { return 0; }
    if (i >= 31) { return 0; }
    if (kind == 0) {
      res = bb_lsh_stage(st, st->stk[yb + i], 1 << i, res, nb);
    } else {
      res = bb_rsh_stage(st, arith, xb, nx, st->stk[yb + i], 1 << i, res, nb);
    }
    if (res == NOID) { return 0; }
  }
  ok = bb_list_eq(st, res, nb, xb, nx);
  return ok;
}

/-- `bbTerm st bi a bs`, `bs` the bits of the `from_bool` node `b`. -/
def bbTerm : Fn := c_fn% u32 bb_term(struct ck *st, u32 a, u32 b) {
  u32 hdr; u32 code; u32 n; u32 nb; u32 i; u32 x; u32 y; u32 nx; u32 ny;
  u32 bsb; u32 xb; u32 yb; u32 ok;
  hdr = st->pool[a];
  code = hdr & 0xff;
  n = (hdr >> 8) & 0xff;
  nb = (st->pool[b] >> 8) & 0xff;
  if (code == BV_VAR) {
    ok = bb_var(st, a, b);
    return ok;
  }
  if (code == BV_VAL) {
    ok = bb_val(st, a, b);
    return ok;
  }
  if (code == BV_ITE) {
    if (n != 3) { return 0; }
    x = st->pool[a + 2];
    y = st->pool[a + 3];
    if ((st->pool[x] & 0xff) != BV_FROM_BOOL || (st->pool[y] & 0xff) != BV_FROM_BOOL) {
      return 0;
    }
    ok = bb_ite(st, st->pool[a + 1], x, y, b);
    return ok;
  }
  while (i < n) {
    x = st->pool[a + 1 + i];
    if ((st->pool[x] & 0xff) != BV_FROM_BOOL) { return 0; }
    i = i + 1;
  }
  if (code == BV_AND) {
    ok = bb_bitwise(st, BOOL_CONJ, a, b);
    return ok;
  }
  if (code == BV_OR) {
    ok = bb_bitwise(st, BOOL_DISJ, a, b);
    return ok;
  }
  if (code == BV_XOR) {
    ok = bb_bitwise(st, BOOL_XOR, a, b);
    return ok;
  }
  if (code == BV_CONCAT) {
    ok = bb_concat(st, a, b);
    return ok;
  }
  if (code == BV_EXTRACT) {
    if (n != 1) { return 0; }
    ok = bb_extract(st, hdr >> 24, (hdr >> 16) & 0xff, st->pool[a + 1], b);
    return ok;
  }
  if (code == BV_SEXT) {
    if (n != 1) { return 0; }
    ok = bb_sext(st, st->pool[a + 1], b, hdr >> 24);
    return ok;
  }
  bsb = st->sp;
  ok = push_args(st, b);
  if (ok == 0) { return 0; }
  if (code == BV_ADD) {
    ok = bb_add(st, a, bsb, nb);
    return ok;
  }
  if (code == BV_NOT || code == BV_NEG) {
    if (n != 1) { return 0; }
    x = st->pool[a + 1];
    nx = (st->pool[x] >> 8) & 0xff;
    xb = st->sp;
    ok = push_args(st, x);
    if (ok == 0) { return 0; }
    if (code == BV_NOT) {
      ok = bb_zip_not(st, bsb, nb, xb, nx);
    } else {
      ok = bb_neg(st, xb, nx, bsb, nb);
    }
    return ok;
  }
  if (code == BV_SUB || code == BV_SHL || code == BV_LSHR || code == BV_ASHR) {
    if (n != 2) { return 0; }
    x = st->pool[a + 1];
    nx = (st->pool[x] >> 8) & 0xff;
    xb = st->sp;
    ok = push_args(st, x);
    if (ok == 0) { return 0; }
    y = st->pool[a + 2];
    ny = (st->pool[y] >> 8) & 0xff;
    yb = st->sp;
    ok = push_args(st, y);
    if (ok == 0) { return 0; }
    if (code == BV_SUB) {
      ok = bb_sub(st, xb, nx, yb, ny, bsb, nb);
    } else if (code == BV_SHL) {
      ok = bb_shift(st, 0, xb, nx, yb, ny, bsb, nb);
    } else if (code == BV_LSHR) {
      ok = bb_shift(st, 1, xb, nx, yb, ny, bsb, nb);
    } else {
      ok = bb_shift(st, 2, xb, nx, yb, ny, bsb, nb);
    }
    return ok;
  }
  return 0;
}

/-- `bbAtom.eqBits st cs xs ys`, with `cs` the arguments of the `conj` node
`b` and `xs`, `ys` the bits of the `from_bool` nodes `x`, `y`. -/
def bbEqBits : Fn := c_fn% u32 bb_eq_bits(struct ck *st, u32 b, u32 x, u32 y) {
  u32 n; u32 i; u32 ok;
  n = (st->pool[b] >> 8) & 0xff;
  if (n != ((st->pool[x] >> 8) & 0xff) || n != ((st->pool[y] >> 8) & 0xff)) { return 0; }
  while (i < n) {
    ok = bb_is2(st, st->pool[b + 1 + i], BB_EQ2, st->pool[x + 1 + i], st->pool[y + 1 + i]);
    if (ok == 0) { return 0; }
    i = i + 1;
  }
  return 1;
}

/-- `bbAtom st a b`. -/
def bbAtom : Fn := c_fn% u32 bb_atom(struct ck *st, u32 a, u32 b) {
  u32 code; u32 n; u32 x; u32 y; u32 nx; u32 ny; u32 xb; u32 yb; u32 ok;
  n = bb_nargs(st, a);
  if (n != 2) { return 0; }
  x = st->pool[a + 1];
  y = st->pool[a + 2];
  if ((st->pool[x] & 0xff) != BV_FROM_BOOL || (st->pool[y] & 0xff) != BV_FROM_BOOL) {
    return 0;
  }
  code = st->pool[a] & 0xff;
  if (code == BOOL_EQ) {
    if ((st->pool[b] & 0xff) != BOOL_CONJ) { return 0; }
    ok = bb_eq_bits(st, b, x, y);
    return ok;
  }
  if (code != BOOL_ULT && code != BOOL_ULE && code != BOOL_SLT && code != BOOL_SLE) {
    return 0;
  }
  nx = (st->pool[x] >> 8) & 0xff;
  ny = (st->pool[y] >> 8) & 0xff;
  xb = st->sp;
  ok = push_args(st, x);
  if (ok == 0) { return 0; }
  yb = st->sp;
  ok = push_args(st, y);
  if (ok == 0) { return 0; }
  if (code == BOOL_ULT) {
    ok = bb_ult(st, 0, xb, nx, yb, ny, b);
  } else if (code == BOOL_ULE) {
    ok = bb_ult(st, 1, xb, nx, yb, ny, b);
  } else if (code == BOOL_SLT) {
    ok = bb_slt(st, 0, xb, nx, yb, ny, b);
  } else {
    ok = bb_slt(st, 1, xb, nx, yb, ny, b);
  }
  return ok;
}

/-- `ruleBitblast`. -/
def rBitblast : Fn := c_fn% u32 r_bitblast(struct ck *st, u32 np, u32 na) {
  u32 e; u32 a; u32 b; u32 t; u32 ok;
  if (np != 0 || na != 1) { return NOID; }
  e = expr_at(st, st->par[0]);
  if (e == NOID) { return NOID; }
  if ((st->pool[e] & 0xff) != BOOL_EQ) { return NOID; }
  a = st->pool[e + 1];
  b = st->pool[e + 2];
  t = ty_of(st->pool[a]);
  if (t < TY_BOOL) {
    if ((st->pool[b] & 0xff) != BV_FROM_BOOL) { return NOID; }
    ok = bb_term(st, a, b);
  } else if (t == TY_BOOL) {
    ok = bb_atom(st, a, b);
  } else {
    return NOID;
  }
  if (ok == 0) { return NOID; }
  return e;
}

def bitblastFns : List Fn :=
  [bbNargs, bbIs1, bbIs2, bbVar, bbVal, bbIteBit, bbIte, bbZipNot, bbListEq, bbPre, bbCarry,
   bbRipple, bbAdd, bbNeg, bbSub, bbBitwise, bbConcat, bbExtract, bbSext, bbUltBase, bbUlt,
   bbSlt, bbIsFill, bbShiftLimit, bbLog2, bbLshStage, bbRshStage, bbShift, bbTerm, bbEqBits,
   bbAtom, rBitblast]

end Vbcf
