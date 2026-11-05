# Keel

A verified in-kernel proof checker for proof-carrying BPF.

The Linux eBPF verifier rejects a safe program when its abstract domains cannot
prove a safety condition. Systems such as [BCF](https://github.com/SunHao-0/BCF)
address this with proof-carrying code. A solver in user space produces a
certificate that the condition holds, and a small checker in the kernel checks
that certificate. The certificate is untrusted, so a bug in the checker can
compromise the kernel.

Keel replaces BCF's checker with one that has machine-checked proofs. It reads
BCF's binary certificate format and is printed as C from a Lean development.

## What is proved

For every refinement condition, every certificate of `B` bytes (condition
included) and every allowed kernel API behavior, including allocation and copy
failures:

1. **Logical soundness:** Keel accepts only if the condition is unsatisfiable
   under bit-vector semantics.
2. **Memory and undefined-behavior safety:** the C triggers no undefined behavior
   and frees every block it allocates.
3. **Linear resource bounds:** the C terminates within `O(B)` time and `O(B)`
   memory.

| Result | Lean theorem | File |
| --- | --- | --- |
| Soundness of the functional checker | `Bcf.checkBcf_sound` | `Bcf/Final.lean` |
| Refinement and safety of the EmbC checker | `Vbcf.Proof.vbcf_check_proof_sound'` | `Vbcf/Proof/Final.lean` |
| Cost bound | `Vbcf.Proof.vbcf_check_proof_sound_bounded` | `Vbcf/Proof/CostFinal.lean` |
| EmbC and Clight: equivalence on safe inputs | `EmbC.Clight.embc_clight_behavior_equivalence` | `EmbC/Clight.lean` |
| EmbC and Clight: reflection of Clight undefined behavior | `EmbC.Clight.clight_ub_modeled_in_embc` | `EmbC/Clight.lean` |
| The checker's guarantees carried to Clight | `Vbcf.Proof.vbcf_check_proof_clight` | `Vbcf/Proof/ClightFinal.lean` |

**What is trusted:**

- the eBPF verifier that constructs the refinement condition
- the bit-vector semantics (`Bcf/Semantics.lean`) and certificate decoder (`Bcf/Format.lean`)
- the EmbC semantics (`EmbC/Semantics.lean`, `EmbC/Eval.lean`, `EmbC/Memory.lean`)
- the kernel API specifications (`EmbC/Kernel.lean`)
- the EmbC-to-C printer (`EmbC/Print.lean`)
- the hand-written kernel glue (`Vbcf/c/bcf_check_proof.h`, `kernel/bpf-config-vbcf.patch`)
- the C compiler
- Lean, and for the Clight results, the [Clean](https://github.com/Certora/clean) Clight model

The rule implementations, the rewrite table and the replay loop are not trusted;
each has a proof.

## Repository layout

| Path | Contents |
| --- | --- |
| `Bcf/` | The functional checker in Lean: terms, semantics, decoder, one function per inference rule, and the soundness proofs. `Bcf/Rw/` holds the rewrite table and one soundness theorem per rewrite. |
| `EmbC/` | A deep embedding of a small C subset: syntax, semantics, kernel API contracts, program logic, cost model and C printer. `EmbC/Clight/` relates it to CompCert's Clight. |
| `Vbcf/` | The checker written in EmbC (`Vbcf` is Keel's name in the code). |
| `Vbcf/Proof/` | The refinement, safety and cost proofs of that checker. `Vbcf/Proof/README.md` maps the files. |
| `Vbcf/c/vbcf.c` | The generated C. Do not edit it; regenerate it with `Vbcf/c/build.sh`. |
| `Vbcf/c/`, `Vbcf/tests/`, `tests/` | User-space drivers, comparison scripts and test-certificate generators. |
| `kernel/` | The patch and build script that put the checker in a Linux kernel. |
| `tools/conv.py` | Transcribes BCF's rewrite header into Lean table entries. |

## Building and checking the proofs

Install [elan](https://github.com/leanprover/elan); `lean-toolchain` pins Lean 4.34.

`lake build` builds the libraries and `bcfcheck`, but not the checker's proofs.
To check those too:

```bash
lake build
```

```bash
lake build Vbcf.Proof.ClightFinal Vbcf.Proof.CostFinal vbcf
```

```bash
lake env lean Vbcf/Proof/Axioms.lean
```

The last command prints the axioms behind each theorem in the table above.

## Running the checker

The Lean checker takes certificate files and prints `accepted N of M`. `--diag`
reports the first failing step and `--trace` prints every step.

```bash
.lake/build/bin/bcfcheck certificate.bcf
```

`build.sh` prints the C again from Lean and compiles the user-space driver. The
driver prints the checker's return value, which is `0` when it accepts, and the
number of blocks still allocated.

```bash
sh Vbcf/c/build.sh
```

```bash
Vbcf/c/vbcf_c certificate.bcf
```

## Testing

BCF's repository has a [corpus of real certificates](https://github.com/SunHao-0/BCF/tree/main/bcf-proofs).
All of these run from the repository root, after `Vbcf/c/build.sh`.

Compare the C and Lean checkers step by step:

```bash
sh Vbcf/c/corpus.sh <certificate-dir>
```

Compare the compiled C with the EmbC interpreter, with kernel call failures injected:

```bash
sh Vbcf/c/interp_test.sh <certificate-dir> 6000 12
```

Run generated certificates for rules the corpus does not reach:

```bash
sh Vbcf/tests/run_gen.sh
```

Test the printed EmbC example against the interpreter:

```bash
sh EmbC/c/run_tests.sh
```

## Running in the kernel

Keel targets Linux 6.19-rc1 on x86 (bpf-next commit `317a5df78f24`) with BCF's
patch sets 1–5. `kernel/build.sh` applies those patches, adds Keel behind
`CONFIG_BPF_VBCF`, and builds the kernel and `bpftool`. It needs a bpf-next
checkout and a clone of the BCF repository. Set `CHECKER=bcf` to build the same
kernel with BCF's checker.

```bash
sh kernel/build.sh <bpf-next> <BCF> <work-dir>
```

To load programs, boot the kernel with BCF's VM image and scripts (see the
[BCF repository](https://github.com/SunHao-0/BCF)).

## License

MIT; see [LICENSE](LICENSE).
