# Tests

`mk_shift_tests.py <outdir>` writes small `.bcf` proofs that exercise the
BITBLAST rule on shifts and bit-vector ite (`ASSUME ¬E; BITBLAST E; CONTRA`),
building the circuits independently of the Lean checker from the description of
`bb_shift_limit`, `bb_bv_lsh`, `bb_rsh` and `bb_bv_ite` in `bcf_checker.c`.
The nine `*_w*.bcf` files must be accepted and the four `BAD_*.bcf` files
(wrong fill bit, swapped output bits, swapped ite branches) must be rejected:

```bash
python3 tests/mk_shift_tests.py /tmp/bbtest && for f in /tmp/bbtest/*.bcf; do printf '%s: ' $(basename $f); .lake/build/bin/bcfcheck $f >/dev/null 2>&1 && echo accepted || echo rejected; done
```

The corpus test uses the 1,891 proofs in BCF's repository,
<https://github.com/SunHao-0/BCF/tree/main/bcf-proofs>; see the top-level README.

`mk_cost_witnesses.py <aci|poly|eval|absorb> <K> <out.bcf>` writes a valid ~50-word proof whose one
normalisation step is exponential in `K` for a checker that walks the shared DAG as a tree
(`x_k = op(x_{k-1}, x_{k-1})`). The Lean checker accepts them (2.3 s at `K` = 22 for `aci` and `poly`,
doubling per level; `eval` is memoised). The C checker rejects `aci` from `K` = 11 (more than
`MAX_SORT` operands), `poly` from `K` = 15 and `eval` from `K` = 20 (the work budget, 128 units per
input word plus `WORK_BASE` = 2^20, runs out), and accepts `absorb` at every `K`. They document the
price of the work budget.
