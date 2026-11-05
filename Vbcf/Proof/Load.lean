import Vbcf.Proof.Load1
import Vbcf.Proof.Load2
import Vbcf.Proof.Load3
import Vbcf.Proof.Load4
import Vbcf.Proof.Load5
import Vbcf.Proof.DLoad1
import Vbcf.Proof.DLoad2
import Vbcf.Proof.DScan

/-!
# Vbcf proofs: the loading phase

* `Load1` — `Holds.calloc`, `Holds.setProof`, `ck_init_spec : InitSpec`;
* `Load2` — `ck_scan_spec : ScanSpec'` (`ScanSpec` is unprovable: `ScanDone.false`,
  `scanSpec_iff`), `expr_at_load`;
* `Load3` — the candidate `ck_load` writes (`LoadWritten`), `ck_intern`'s
  precondition for it, and `LoadWritten.loadNode`: the node `ck_intern`
  reports is the Lean loader's `loadNode`;
* `Load4` — `ck_load`'s loop invariant `LoadState`, one iteration
  (`LoadState.step`), the exit (`LoadState.done`);
* `Load5` — `ck_load_spec : LoadSpec`.

The structural contracts used by the direct soundness proof (`DSpecs`):

* `Load1` — `ck_init_dspec : DInitSpec`;
* `DLoad1` — `ck_load`'s structural loop invariant `DLoadState`;
* `DLoad2` — `ck_load_dspec : DLoadSpec`;
* `DScan` — `ck_scan_dspec : DScanSpec`, `expr_at_dload`.
-/
