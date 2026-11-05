import EmbC.Print
import EmbC.Testing.Kernel
import EmbC.Examples.Vec

/-!
# Stage 1 driver

`embc_example print` writes the example program as C.
`embc_example run <n> <k>*` runs `test_driver(n)` in the Lean interpreter,
failing the allocations whose (0-based) sequence numbers are listed.

`EmbC/c/run_tests.sh` compiles the printed C and checks that both agree.
-/

namespace EmbC.Examples
open EmbC

/-- Unverified test code: drives the verified functions and folds everything
they return into one number. -/
def testDriver : Fn := c_fn% u32 test_driver(u32 n) {
  struct vec *v; u32 i; u32 h; u32 r; u32 *d;
  v = kzalloc(sizeof(struct vec));
  if (v == NULL) { return 4294967295; }
  while (i < n) {
    r = vec_push2(v, i * 7 + 1, i * 13 + 2);
    h = h * 31 + r;
    i = i + 1;
  }
  i = 0;
  while (i < v->len) {
    h = h * 31 + v->data[i];
    i = i + 1;
  }
  d = v->data;
  if (d != NULL) {
    r = words_eq(d, d, v->len);
    h = h * 31 + r;
    if (v->len > 1) {
      r = words_eq(d, d +> 1, v->len - 1);
      h = h * 31 + r;
    }
  }
  h = h ^ (v->len << 16) ^ (u32)((u64)v->cap * 3ull >> 1ull);
  kvfree(d);
  kvfree(v);
  return h;
}

def testProg : Prog := { prog with fns := prog.fns ++ [testDriver] }

def runDriver (n : Nat) (fails : List Nat) : String :=
  let world : Testing.World := { failingCalls := fails }
  match testProg.run 1000000 "test_driver" [.u32 (BitVec.ofNat 32 n)] ⟨Mem.empty, Testing.oracle testProg world⟩ with
  | .timeout => "timeout"
  | .stuck => "stuck"
  | .ok (some (.u32 v), st) =>
    let live := st.mem.blocks.toList.filter Option.isSome |>.length
    s!"{v.toNat} live={live}"
  | .ok _ => "bad result"

end EmbC.Examples

open EmbC.Examples in
def main (args : List String) : IO UInt32 := do
  match args with
  | ["print"] =>
    match EmbC.Prog.toC testProg with
    | .ok s => IO.print s; pure 0
    | .error e => IO.eprintln e; pure 1
  | "run" :: n :: fails =>
    IO.println (runDriver n.toNat! (fails.map String.toNat!)); pure 0
  | _ => IO.eprintln "usage: embc_example print | run <n> <failing-alloc-index>*"; pure 2
