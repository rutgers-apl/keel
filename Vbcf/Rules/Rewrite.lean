import Vbcf.Rules.Eval
import Vbcf.Enc
import Bcf.Rw.Table

/-!
# Vbcf rules: REWRITE

`r_rewrite` is `Bcf.ruleRewrite` (`Bcf/Check.lean`).  The rewrite table is not
written in C: it is *data*, the constant table `rw_tbl`, computed here from the
verified `Bcf.rwTable` by `RwEnc.encTable`.  The C functions are an interpreter
of that encoding which mirrors `instE` / `instA` / `pushApp` / `pushLit` /
`paramsOK` / `checkCond` / `rwConclude` (`Bcf/Rw/Pattern.lean`, `Bcf/Check.lean`).

## Encoding of `rw_tbl`

* Words `0 .. RW_NRULES-1` are the index: word `i` is the offset of the record
  of rewrite `i`, or 0 if `Bcf.rwTable i = none`.
* A record at offset `o`:
  `[nparams, cond, lhs, rhs, ty_0, …, ty_{nparams-1}, expressions…]`,
  where `cond`, `lhs`, `rhs` are absolute offsets of encoded patterns
  (`cond` is 0 when absent) and `ty_k` is an encoded `RwTy`
  (`RW_ANY`, `RW_BOOL`, `RW_BVQ`, `RW_BOOLS`, `RW_BVQS`, or `RW_BV | w << 8`).
* A pattern (`RwExpr`) is in prefix form.  Its first word is
  `tag | aux << 8 | len << 16`, where `len` is the number of words of the whole
  pattern including this one; the sub-patterns follow in order, so the next
  sibling of the pattern at `p` is at `p + (rw_tbl[p] >> 16)`.
  `aux` is the variable number for `RW_VAR`, and for `RW_APP` the node code of
  the operator (`opCode (op.node 0)`), from which `rw_app` recovers
  `RwOp.reducible`, `RwOp.node` and `RwOp.width`.  `RW_LIT` has one more word,
  the literal's value.

Lean lists of node ids are ranges of the scratch stack: the rule's arguments
are `stk[ab .. ab+na)`, and the instantiated (spliced) arguments of an operator
are pushed on top while it is being built.

## Where the C is stricter than Lean

* a constant that `cval` cannot evaluate (wider than 64 bits, or nested deeper
  than `MAX_DEPTH`) rejects the step; Lean's `constNat` may succeed;
* a computed width above 255 (`sumBv` of a concatenation, `n + k` of an
  extension, `m * k` of a repeat) rejects the step; Lean's widths are unbounded;
* an operator with more than 255 spliced arguments rejects the step.

`Bcf.noVars` is not used by `ruleRewrite` and has no C counterpart.
-/

namespace Vbcf
open EmbC

/-! ## The encoder (specification side) -/

namespace RwEnc

def tVar : Nat := 0
def tTT : Nat := 1
def tFF : Nat := 2
def tLit : Nat := 3
def tSymVal : Nat := 4
def tBvmax : Nat := 5
def tApp : Nat := 6
def tIte : Nat := 7
def tExtract : Nat := 8
def tZext : Nat := 9
def tSext : Nat := 10
def tRepeat : Nat := 11

def yAny : Nat := 0
def yBool : Nat := 1
def yBv : Nat := 2
def yBvq : Nat := 3
def yBools : Nat := 4
def yBvqs : Nat := 5

/-- Number of rewrite ids covered by the index (`Bcf.rwTable i = none` for `i ≥ bound`). -/
def bound : Nat := 166

/-- Words before the parameter types in a rule record. -/
def recHdr : Nat := 4

def hdr (tag aux len : Nat) : Nat := tag ||| (aux <<< 8) ||| (len <<< 16)

mutual
def encE : Bcf.RwExpr → List Nat
  | .var i => [hdr tVar i 1]
  | .tt => [hdr tTT 0 1]
  | .ff => [hdr tFF 0 1]
  | .lit v => [hdr tLit 0 2, v]
  | .symVal val sz =>
    let b := encE val ++ encE sz
    hdr tSymVal 0 (b.length + 1) :: b
  | .bvmax sz =>
    let b := encE sz
    hdr tBvmax 0 (b.length + 1) :: b
  | .app op as =>
    let b := encA as
    hdr tApp (opCode (op.node 0)).1 (b.length + 1) :: b
  | .ite c t e =>
    let b := encE c ++ encE t ++ encE e
    hdr tIte 0 (b.length + 1) :: b
  | .extract hi lo x =>
    let b := encE hi ++ encE lo ++ encE x
    hdr tExtract 0 (b.length + 1) :: b
  | .zext e x =>
    let b := encE e ++ encE x
    hdr tZext 0 (b.length + 1) :: b
  | .sext e x =>
    let b := encE e ++ encE x
    hdr tSext 0 (b.length + 1) :: b
  | .repeat n x =>
    let b := encE n ++ encE x
    hdr tRepeat 0 (b.length + 1) :: b
def encA : Bcf.RwArgs → List Nat
  | .nil => []
  | .cons a rest => encE a ++ encA rest
end

def encTy : Bcf.RwTy → Nat
  | .any => yAny
  | .bool => yBool
  | .bv w => yBv ||| (w <<< 8)
  | .bvq => yBvq
  | .bools => yBools
  | .bvqs => yBvqs

def encOpt : Option Bcf.RwExpr → List Nat
  | none => []
  | some e => encE e

/-- The record of rule `r`, placed at absolute offset `off`. -/
def encRule (off : Nat) (r : Bcf.RwRule) : List Nat :=
  let ps := r.params.map encTy
  let c := encOpt r.cond
  let l := encE r.lhs
  let e0 := off + recHdr + ps.length
  let coff := if r.cond.isSome then e0 else 0
  let loff := e0 + c.length
  let roff := loff + l.length
  [ps.length, coff, loff, roff] ++ ps ++ c ++ l ++ encE r.rhs

/-- Index and records of the rules with id `< n`. -/
def encUpTo (tbl : Nat → Option Bcf.RwRule) : Nat → List Nat × List Nat
  | 0 => ([], [])
  | n + 1 =>
    let (idx, body) := encUpTo tbl n
    match tbl n with
    | none => (idx ++ [0], body)
    | some r => (idx ++ [bound + body.length], body ++ encRule (bound + body.length) r)

/-- The whole table: the index followed by the records. -/
def encTable (tbl : Nat → Option Bcf.RwRule) : List Nat :=
  let (idx, body) := encUpTo tbl bound
  idx ++ body

/-- The words of `rw_tbl`. -/
def words : List Nat := encTable Bcf.rwTable

end RwEnc

/-- The rewrite table as a C constant. -/
def rwTblDef : ConstDef := ⟨"rw_tbl", (RwEnc.words.map (BitVec.ofNat 32)).toArray⟩

-- Every word fits in 32 bits (so `rwTblDef` loses nothing), and the index is complete.
#guard RwEnc.words.all (· < 2 ^ 32)
#guard (List.range RwEnc.bound).all fun i => (RwEnc.words[i]! != 0) == (Bcf.rwTable i).isSome
#guard (List.range 4096).all fun i => i < RwEnc.bound || (Bcf.rwTable i).isNone

c_const% RW_NRULES := BitVec.ofNat 32 RwEnc.bound
c_const% RW_REC := BitVec.ofNat 32 RwEnc.recHdr

c_const% RW_VAR := BitVec.ofNat 32 RwEnc.tVar
c_const% RW_TT := BitVec.ofNat 32 RwEnc.tTT
c_const% RW_FF := BitVec.ofNat 32 RwEnc.tFF
c_const% RW_LIT := BitVec.ofNat 32 RwEnc.tLit
c_const% RW_SYMVAL := BitVec.ofNat 32 RwEnc.tSymVal
c_const% RW_BVMAX := BitVec.ofNat 32 RwEnc.tBvmax
c_const% RW_APP := BitVec.ofNat 32 RwEnc.tApp
c_const% RW_ITE := BitVec.ofNat 32 RwEnc.tIte
c_const% RW_EXTRACT := BitVec.ofNat 32 RwEnc.tExtract
c_const% RW_ZEXT := BitVec.ofNat 32 RwEnc.tZext
c_const% RW_SEXT := BitVec.ofNat 32 RwEnc.tSext
c_const% RW_REPEAT := BitVec.ofNat 32 RwEnc.tRepeat

c_const% RW_ANY := BitVec.ofNat 32 RwEnc.yAny
c_const% RW_BOOL := BitVec.ofNat 32 RwEnc.yBool
c_const% RW_BV := BitVec.ofNat 32 RwEnc.yBv
c_const% RW_BVQ := BitVec.ofNat 32 RwEnc.yBvq
c_const% RW_BOOLS := BitVec.ofNat 32 RwEnc.yBools
c_const% RW_BVQS := BitVec.ofNat 32 RwEnc.yBvqs

/-! ## Instantiation -/

/-- `Bcf.constNat`: 1 if node `id` is a constant bit-vector, its value then in
`st->val`; else 0.  Also 0 when the C checker cannot evaluate the node (`cval`
returns `NOID`).  Every caller rejects the step on 0, exactly where Lean
rejects on `none`, so the two cases need not be told apart. -/
def rwConst : Fn := c_fn% u32 rw_const(struct ck *st, u32 id) {
  u32 cw;
  cw = cval(st, id, MAX_DEPTH);
  if (cw == 0 || cw > 64) { return 0; }
  return 1;
}

/-- `Bcf.pushLit st sz v`: the literal of width `sz` and value `v`.  `pushNode`
requires `1 ≤ sz ≤ 64` and `v < 2 ^ sz`. -/
def rwLit : Fn := c_fn% u32 rw_lit(struct ck *st, u64 sz, u64 v) {
  u32 r;
  if (sz > 255ull) { return NOID; }
  if (sz == 0ull || sz > 64ull) { return NOID; }
  if (sz < 64ull && (v >> sz) != 0ull) { return NOID; }
  r = mkval(st, (u32)sz, v);
  return r;
}

/-- `Bcf.spliceIdx`: push the elements contributed by the argument node `i`
(the elements of a list node, else `i` itself).  Returns 0 on failure. -/
def rwSplice : Fn := c_fn% u32 rw_splice(struct ck *st, u32 i) {
  u32 t; u32 ok;
  t = ty_of(st->pool[i]);
  if (t >= TY_LIST) {
    if ((st->pool[i] & 0xff) != LIST_VAL) { return 0; }
    ok = push_args(st, i);
    return ok;
  }
  ok = push(st, i);
  return ok;
}

/-- `Bcf.pushApp st op is`, where `is` is `stk[base..base+n)` and `code` is the
node code of `op` (`opCode (op.node 0)`).  The header parameter is
`RwOp.width`: `sumBv` for concatenation, 32 for `bvsize`, `firstBv` for the
other bit-vector operators; boolean operators have no parameter. -/
def rwApp : Fn := c_fn% u32 rw_app(struct ck *st, u32 code, u32 base, u32 n) {
  u32 i; u32 t; u32 w; u32 r;
  if (n == 0) { return NOID; }
  if (n == 1) {
    if (code == BOOL_CONJ || code == BOOL_DISJ || code == BOOL_XOR || code == BV_ADD
        || code == BV_MUL || code == BV_OR || code == BV_AND || code == BV_XOR
        || code == BV_CONCAT) {
      return st->stk[base];
    }
  }
  if (n > 255) { return NOID; }
  if (code == BV_CONCAT) {
    while (i < n) {
      t = ty_of(st->pool[st->stk[base + i]]);
      if (t >= TY_BOOL) { break; }
      w = w + t;
      i = i + 1;
    }
  } else if (code == BV_SIZE) {
    w = 32;
  } else if ((code & 7) == 0) {
    while (i < n) {
      t = ty_of(st->pool[st->stk[base + i]]);
      if (t < TY_BOOL) {
        w = t;
        break;
      }
      i = i + 1;
    }
  }
  if (w > 255) { return NOID; }
  r = mkn(st, code | (w << 16), base, n);
  return r;
}

/-- The end of `Bcf.instE` for `.symVal val sz`: `a` and `b` are the
instantiated `val` and `sz`. -/
def rwSym : Fn := c_fn% u32 rw_sym(struct ck *st, u32 a, u32 b) {
  u32 ok; u32 r; u64 x; u64 y;
  ok = rw_const(st, a);
  if (ok == 0) { return NOID; }
  x = st->val;
  ok = rw_const(st, b);
  if (ok == 0) { return NOID; }
  y = st->val;
  r = rw_lit(st, y, x);
  return r;
}

/-- The end of `Bcf.instE` for `.bvmax sz`: `a` is the instantiated `sz`.
The value `2 ^ sn - 1` is only computed for `1 ≤ sn ≤ 64`; for other sizes
`pushLit` fails. -/
def rwMax : Fn := c_fn% u32 rw_max(struct ck *st, u32 a) {
  u32 ok; u32 r; u64 x; u64 y;
  ok = rw_const(st, a);
  if (ok == 0) { return NOID; }
  y = st->val;
  if (y == 0ull || y > 64ull) { return NOID; }
  x = mask64((u32)y);
  r = rw_lit(st, y, x);
  return r;
}

/-- The end of `Bcf.instE` for `.zext e x`, `.sext e x` and `.repeat n x`:
`a` is the instantiated count and `b` the operand.  A result wider than 255
bits does not fit a node header and is rejected. -/
def rwExt : Fn := c_fn% u32 rw_ext(struct ck *st, u32 tag, u32 a, u32 b) {
  u32 ok; u32 r; u32 t; u32 k; u64 x;
  ok = rw_const(st, a);
  if (ok == 0) { return NOID; }
  x = st->val;
  t = ty_of(st->pool[b]);
  if (t >= TY_BOOL) { return NOID; }
  if (x > 255ull) { return NOID; }
  k = (u32)x;
  if (tag == RW_REPEAT) {
    if (t * k > 255) { return NOID; }
    r = mk1(st, BV_REPEAT | ((t * k) << 16) | (k << 24), b);
    return r;
  }
  if (t + k > 255) { return NOID; }
  if (tag == RW_ZEXT) {
    r = mk1(st, BV_ZEXT | ((t + k) << 16) | (k << 24), b);
    return r;
  }
  r = mk1(st, BV_SEXT | ((t + k) << 16) | (k << 24), b);
  return r;
}

/-- The end of `Bcf.instE` for `.ite c t e`: `a`, `b`, `c` are the
instantiated condition and branches. -/
def rwIte : Fn := c_fn% u32 rw_ite(struct ck *st, u32 a, u32 b, u32 c) {
  u32 t; u32 r;
  t = ty_of(st->pool[b]);
  if (t == TY_BOOL) {
    r = mk3(st, BOOL_ITE, a, b, c);
    return r;
  }
  if (t < TY_BOOL) {
    r = mk3(st, BV_ITE | (t << 16), a, b, c);
    return r;
  }
  return NOID;
}

/-- The end of `Bcf.instE` for `.extract hi lo x`: `a`, `b` are the
instantiated `hi`, `lo` and `c` the operand. -/
def rwExtract : Fn := c_fn% u32 rw_extract(struct ck *st, u32 a, u32 b, u32 c) {
  u32 ok; u32 r; u64 x; u64 y;
  ok = rw_const(st, a);
  if (ok == 0) { return NOID; }
  x = st->val;
  ok = rw_const(st, b);
  if (ok == 0) { return NOID; }
  y = st->val;
  if (x > 255ull || y > 255ull) { return NOID; }
  r = mk1(st, BV_EXTRACT | ((u32)y << 16) | ((u32)x << 24), c);
  return r;
}

/-- `Bcf.instE` (and `Bcf.instA`, the loop of the `RW_APP` case) for the
pattern at offset `pos` of `rw_tbl`.  The rule's arguments are
`stk[ab..ab+na)`.  Returns the node, or `NOID`.  `st->sp` is the same on a
successful return as on entry.

As in Lean, the sub-patterns are instantiated first, left to right, and the
node is built last (`rw_app`, `rw_sym`, `rw_max`, `rw_ext`, `rw_ite`,
`rw_extract`).  The recursion is over the pattern, whose depth is at most 9
in `rw_tbl`; `depth` bounds it. -/
def rwInst : Fn := c_fn% u32 rw_inst(struct ck *st, u32 pos, u32 ab, u32 na, u32 depth) {
  u32 hdr; u32 tag; u32 aux; u32 endp; u32 p; u32 a; u32 b; u32 c; u32 base; u32 ok; u32 r;
  if (depth == 0) { return NOID; }
  hdr = @rw_tbl[pos];
  tag = hdr & 0xff;
  aux = (hdr >> 8) & 0xff;
  endp = pos + (hdr >> 16);
  if (tag > RW_REPEAT) { return NOID; }
  if (tag == RW_VAR) {
    if (aux >= na) { return NOID; }
    return st->stk[ab + aux];
  }
  if (tag == RW_TT) { return st->tt; }
  if (tag == RW_FF) { return st->ff; }
  if (tag == RW_LIT) {
    r = mkval(st, 32, (u64)@rw_tbl[pos + 1]);
    return r;
  }
  if (tag == RW_APP) {
    base = st->sp;
    p = pos + 1;
    while (p < endp) {
      a = rw_inst(st, p, ab, na, depth - 1);
      if (a == NOID) { return NOID; }
      ok = rw_splice(st, a);
      if (ok == 0) { return NOID; }
      p = p + (@rw_tbl[p] >> 16);
    }
    r = rw_app(st, aux, base, st->sp - base);
    st->sp = base;
    return r;
  }
  p = pos + 1;
  a = rw_inst(st, p, ab, na, depth - 1);
  if (a == NOID) { return NOID; }
  if (tag == RW_BVMAX) {
    r = rw_max(st, a);
    return r;
  }
  p = p + (@rw_tbl[p] >> 16);
  b = rw_inst(st, p, ab, na, depth - 1);
  if (b == NOID) { return NOID; }
  if (tag == RW_SYMVAL) {
    r = rw_sym(st, a, b);
    return r;
  }
  if (tag == RW_ZEXT || tag == RW_SEXT || tag == RW_REPEAT) {
    r = rw_ext(st, tag, a, b);
    return r;
  }
  p = p + (@rw_tbl[p] >> 16);
  c = rw_inst(st, p, ab, na, depth - 1);
  if (c == NOID) { return NOID; }
  if (tag == RW_ITE) {
    r = rw_ite(st, a, b, c);
    return r;
  }
  if (tag == RW_EXTRACT) {
    r = rw_extract(st, a, b, c);
    return r;
  }
  return NOID;
}

/-! ## Parameters, guard, conditions -/

/-- `Bcf.rwTyOK` for the encoded parameter type `pt` and the node type `t`. -/
def rwTyOk : Fn := c_fn% u32 rw_ty_ok(u32 pt, u32 t) {
  u32 k;
  k = pt & 0xff;
  if (k == RW_ANY) { return 1; }
  if (k == RW_BOOL) { return t == TY_BOOL; }
  if (k == RW_BV) { return t < TY_BOOL && t == (pt >> 8); }
  if (k == RW_BVQ) { return t < TY_BOOL && t <= 255; }
  if (k == RW_BOOLS) { return t >= TY_LIST && ((t >> 8) & 1) == 1; }
  if (k == RW_BVQS) { return t >= TY_LIST && ((t >> 8) & 1) == 0; }
  return 0;
}

/-- `Bcf.paramsOK st r.params args` for the rule record at `off` and the
arguments `stk[ab..ab+na)`. -/
def rwParams : Fn := c_fn% u32 rw_params(struct ck *st, u32 off, u32 ab, u32 na) {
  u32 i; u32 t; u32 ok;
  if (@rw_tbl[off] != na) { return 0; }
  while (i < na) {
    t = ty_of(st->pool[st->stk[ab + i]]);
    ok = rw_ty_ok(@rw_tbl[off + RW_REC + i], t);
    if (ok == 0) { return 0; }
    i = i + 1;
  }
  return 1;
}

/-- `Bcf.condMatch`: the premise `p` is the condition `c`, or `c = true`. -/
def rwCondMatch : Fn := c_fn% u32 rw_cond_match(struct ck *st, u32 c, u32 p) {
  if (p == c) { return 1; }
  if ((st->pool[p] & 0xff) != BOOL_EQ) { return 0; }
  return st->pool[p + 2] == st->tt && st->pool[p + 1] == c;
}

/-- One conjunct `ci` of an instantiated condition, in position `i`: matched by
premise `i` when there is one (`Bcf.condMatch`), otherwise a closed constant that
evaluates to `true` (`Bcf.cval`). -/
def rwCondOne : Fn := c_fn% u32 rw_cond_one(struct ck *st, u32 ci, u32 i, u32 np) {
  u32 ok; u32 cw;
  if (i < np) {
    ok = rw_cond_match(st, ci, st->prem[i]);
    return ok;
  }
  cw = cval(st, ci, MAX_DEPTH);
  if (cw != CV_BOOL) { return 0; }
  return st->val == 1ull;
}

/-- `Bcf.checkCond` (with `Bcf.condsOK`): the instantiated condition `c`, a
conjunction or a single fact, against the premises `st->prem[0..np)`. -/
def rwCheckCond : Fn := c_fn% u32 rw_check_cond(struct ck *st, u32 c, u32 np) {
  u32 n; u32 i; u32 ok;
  if ((st->pool[c] & 0xff) == BOOL_CONJ) {
    n = (st->pool[c] >> 8) & 0xff;
    if (n < np) { return 0; }
    while (i < n) {
      ok = rw_cond_one(st, st->pool[c + 1 + i], i, np);
      if (ok == 0) { return 0; }
      i = i + 1;
    }
    return 1;
  }
  if (np > 1) { return 0; }
  ok = rw_cond_one(st, c, 0, np);
  return ok;
}

/-! ## Rewrite id 0: three fixed shapes -/

/-- `Bcf.andHalf`: `h` is `bvAnd [extract hi lo x, extract hi lo y]`, in either order. -/
def rw0AndHalf : Fn := c_fn% u32 rw0_and_half(struct ck *st, u32 h, u32 x, u32 y, u32 hi, u32 lo) {
  u32 p; u32 q; u32 hp; u32 hq; u32 a; u32 b;
  if ((st->pool[h] & 0xffff) != (BV_AND | (2 << 8))) { return 0; }
  p = st->pool[h + 1];
  q = st->pool[h + 2];
  hp = st->pool[p];
  hq = st->pool[q];
  if ((hp & 0xff) != BV_EXTRACT || (hq & 0xff) != BV_EXTRACT) { return 0; }
  a = st->pool[p + 1];
  b = st->pool[q + 1];
  return (hp >> 24) == hi && (hq >> 24) == hi && ((hp >> 16) & 0xff) == lo
    && ((hq >> 16) & 0xff) == lo && ((a == x && b == y) || (a == y && b == x));
}

/-- `Bcf.rw0AndSplit` (with `Bcf.andPieces`): `x & y` is the concatenation of
`n ≥ 2` pieces `x[hi:lo] & y[hi:lo]`, high to low, contiguous, the first ending
at bit `w - 1` and the last at bit 0. -/
def rw0AndSplit : Fn := c_fn% u32 rw0_and_split(struct ck *st, u32 a, u32 b) {
  u32 w; u32 x; u32 y; u32 n; u32 i; u32 e; u32 h; u32 p; u32 lo; u32 ok;
  if ((st->pool[a] & 0xffff) != (BV_AND | (2 << 8))) { return 0; }
  w = (st->pool[a] >> 16) & 0xff;
  x = st->pool[a + 1];
  y = st->pool[a + 2];
  if ((st->pool[b] & 0xff) != BV_CONCAT) { return 0; }
  if (w != ((st->pool[b] >> 16) & 0xff)) { return 0; }
  n = (st->pool[b] >> 8) & 0xff;
  if (n < 2 || w < 1) { return 0; }
  e = w - 1;
  while (i < n) {
    h = st->pool[b + 1 + i];
    if ((st->pool[h] & 0xffff) != (BV_AND | (2 << 8))) { return 0; }
    p = st->pool[h + 1];
    if ((st->pool[p] & 0xff) != BV_EXTRACT) { return 0; }
    lo = (st->pool[p] >> 16) & 0xff;
    ok = rw0_and_half(st, h, x, y, e, lo);
    if (ok == 0) { return 0; }
    if (i + 1 == n) { return lo == 0; }
    if (lo < 1) { return 0; }
    e = lo - 1;
    i = i + 1;
  }
  return 0;
}

/-- `Bcf.rw0Repeat`: `repeat k y = y ++ … ++ y`. -/
def rw0Repeat : Fn := c_fn% u32 rw0_repeat(struct ck *st, u32 a, u32 b) {
  u32 w; u32 k; u32 y; u32 i;
  if ((st->pool[a] & 0xff) != BV_REPEAT) { return 0; }
  w = (st->pool[a] >> 16) & 0xff;
  k = st->pool[a] >> 24;
  y = st->pool[a + 1];
  if (k == 1) { return b == y; }
  if ((st->pool[b] & 0xff) != BV_CONCAT) { return 0; }
  if (w != ((st->pool[b] >> 16) & 0xff)) { return 0; }
  if (((st->pool[b] >> 8) & 0xff) != k) { return 0; }
  while (i < k) {
    if (st->pool[b + 1 + i] != y) { return 0; }
    i = i + 1;
  }
  return 1;
}

/-- `Bcf.rw0Distinct`: `distinct a b = not (eq a b)`. -/
def rw0Distinct : Fn := c_fn% u32 rw0_distinct(struct ck *st, u32 a, u32 b) {
  u32 e;
  if ((st->pool[a] & 0xff) != BOOL_DISTINCT) { return 0; }
  if ((st->pool[b] & 0xff) != BOOL_NOT) { return 0; }
  e = st->pool[b + 1];
  if ((st->pool[e] & 0xff) != BOOL_EQ) { return 0; }
  return st->pool[a + 1] == st->pool[e + 1] && st->pool[a + 2] == st->pool[e + 2];
}

/-- `Bcf.ruleRewrite0`: `e` is an equation of one of the three trusted shapes. -/
def rwZero : Fn := c_fn% u32 rw_zero(struct ck *st, u32 e) {
  u32 a; u32 b; u32 ok;
  if ((st->pool[e] & 0xff) != BOOL_EQ) { return 0; }
  a = st->pool[e + 1];
  b = st->pool[e + 2];
  ok = rw0_and_split(st, a, b);
  if (ok != 0) { return 1; }
  ok = rw0_repeat(st, a, b);
  if (ok != 0) { return 1; }
  ok = rw0_distinct(st, a, b);
  return ok;
}

/-! ## The rule -/

/-- `Bcf.ruleRewrite` (with `rwConclude`). -/
def rRewrite : Fn := c_fn% u32 r_rewrite(struct ck *st, u32 np, u32 na) {
  u32 rid; u32 off; u32 ab; u32 n; u32 i; u32 a; u32 ok; u32 c; u32 l; u32 r;
  if (na == 0) { return NOID; }
  rid = st->par[0];
  if (rid == 0) {
    if (np != 0 || na != 2) { return NOID; }
    a = expr_at(st, st->par[1]);
    if (a == NOID) { return NOID; }
    ok = rw_zero(st, a);
    if (ok == 0) { return NOID; }
    return a;
  }
  if (rid >= RW_NRULES) { return NOID; }
  off = @rw_tbl[rid];
  if (off == 0) { return NOID; }
  ab = st->sp;
  n = na - 1;
  i = 1;
  while (i < na) {
    a = expr_at(st, st->par[i]);
    if (a == NOID) { return NOID; }
    ok = push(st, a);
    if (ok == 0) { return NOID; }
    i = i + 1;
  }
  ok = rw_params(st, off, ab, n);
  if (ok == 0) { return NOID; }
  c = @rw_tbl[off + 1];
  if (c == 0) {
    if (np != 0) { return NOID; }
  } else {
    c = rw_inst(st, c, ab, n, MAX_DEPTH);
    if (c == NOID) { return NOID; }
    ok = rw_check_cond(st, c, np);
    if (ok == 0) { return NOID; }
  }
  l = rw_inst(st, @rw_tbl[off + 2], ab, n, MAX_DEPTH);
  if (l == NOID) { return NOID; }
  r = rw_inst(st, @rw_tbl[off + 3], ab, n, MAX_DEPTH);
  if (r == NOID) { return NOID; }
  r = mk_eq(st, l, r);
  return r;
}

def rewriteFns : List Fn :=
  [rwConst, rwLit, rwSplice, rwApp, rwSym, rwMax, rwExt, rwIte, rwExtract, rwInst, rwTyOk, rwParams, rwCondMatch, rwCondOne, rwCheckCond,
   rw0AndHalf, rw0AndSplit, rw0Repeat, rw0Distinct, rwZero, rRewrite]

/-- Constant tables used by the rewrite engine. -/
def rewriteConsts : List ConstDef := [rwTblDef]

end Vbcf
