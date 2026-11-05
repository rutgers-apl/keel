import Vbcf.Proof.Hash1
import Vbcf.Proof.Hash2
import Vbcf.Proof.Hash3
import Vbcf.Proof.Hash4
import Vbcf.Proof.Hash5
import Vbcf.Proof.Hash6

/-!
# Vbcf proofs: the hash table and interning

* `Hash1`: `words_eq_spec`, `ck_hash_spec` (and their `Holds` forms
  `words_eq_pool_spec`, `ck_hash_pool_spec`).
* `Hash2`: the table as pure data: `Reach`, `HtabPart`, `Probed`, exact lookup
  (`HtabPart.miss`), insertion (`HtabPart.insert`, `HtabPart.push`), `nzCount`,
  and the mask lemmas (`bv_and_mask`, `probe_start`, `probe_next`).
* `Hash3`: `find_not_spec : FindNotSpec`.
* `Hash4`: `HView` (memory while the old table is detached) and `ck_hput_spec`.
* `Hash5`: `CoreInv'`, `HgrowSpec`, `Holds.swap_htab`, `ck_hgrow_spec : HgrowSpec`.
* `Hash6`: `ck_intern_spec' : TyckSpec → InternSpec'`.

`InternSpec'` is `InternSpec` with `CoreInv` strengthened to `CoreInv'`
(`CoreInv` plus `nzCount c.htab = c.k.hcnt`).  `InternSpec` itself does not
hold: `HtabOK` allows a node to occupy two slots, and from such a state
`ck_hgrow` re-enters it twice, leaving `hcnt ≠ pool.size`.
-/
