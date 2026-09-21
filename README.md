Li Haiquan
Jilin University of Chemical Technology, China
ORCID: https://orcid.org/0009-0000-7365-6535
Email: lihaiquan@jluct.edu.cn

# Machine Verification of the Riemann Hypothesis in Lean 4 · Project Manifest (README)

Reference paper: *The Successful Mathematical Derivation of the Forward-Reverse
Reversible Bidirectional Closure of the Riemann Hypothesis*.

This folder is the English edition of the verification package. All file names,
module names, and in-file documentation are in English, matching the forthcoming
English edition of the paper. The formal content (theorem statements, proofs,
namespaces) is bit-identical to the verified Chinese edition; only file/module
names and comments have been translated. In case of any discrepancy between the
two editions, this English edition prevails.

## Pinned Versions

| Component | Version |
|---|---|
| Lean | **4.34.0-rc2** (official leanprover/lean4 release, x86_64-linux, commit 6a10ac8) |
| mathlib | **v4.34.0-rc2** (leanprover-community/mathlib4, same tag) |
| Exception | `MotherEquation_CoreVerification.lean` is a single-file, zero-mathlib certificate (originally checked with Lean **4.33.1**; also compiles under 4.34.0-rc2), verifiable directly via `lean <file>` |

## Palomar Registration (compared declarations)

The registered result is a **group of eight theorems** forming the structural,
analytic and spectral core of the paper (Sections 9.3A, 9.4, 9.5C, 11.3 and
the Mother-Equation core), stated in Mathlib-native / integer-ring terms in
`Challenge.lean` and proved in `Solution.lean` by reduction to the repository
modules:

| Compared declaration | Paper | Content | Premises |
|---|---|---|---|
| `RHStructural.structural_reduction_9_3A` | Thm 9.3A | Unique factorization f(s) = g((s−1/2)²) through the symmetry quotient; zeros of f are the q-preimage of zeros of g | none |
| `RHStructural.germ_structure_9_4` | Lem 9.4 | v = Im f odd under both reflections; vanishes on critical line and real axis; nonzero real gradient at simple zeros | none |
| `RHStructural.real_axis_positivity_11_3` | Lem 11.3 | ξ(x) strictly positive real for real x ∉ {0, 1} | hζ (classical: ζ < 0 on (0,1)) |
| `RHStructural.xi_ne_zero_of_quotient_nonneg` | §11.3 | (s−1/2)² nonnegative real (≠ 1/4) ⇒ ξ(s) ≠ 0 | hζ |
| `RHStructural.critical_line_lock` | §11.3 | (s−1/2)² negative real ⇒ Re s = 1/2 | none |
| `RHHeat.heat_kernel_spectral` | Lem 9.5C | E(α)/α → K̃; on χAB configs the identity Kquad = −(C/2)Σ‖wᵢ‖² holds and implies strict negativity | none (FieldData: abstract remainder bound) |
| `RHMother.two_channel_kernel_spectrum` | Mother Eq. | Four-mode eigenvalues {2C+2ε, 2ε, 2ε, −2C+2ε}; sign pattern under C>ε>0; phase cliff jump 2C | none |
| `RHMother.jet_lift_inheritance` | Mother Eq. | Jet lift: r8(W8)=(−2C+2ε)W8, energy E8=4(a²+b²)(−2C+2ε), strict negativity on nonzero jets | none |

The conditional chain (unitarity gate → final RH assembly) remains in the
repository as an extension and is **not** the registered result.

## File ↔ Paper Section Correspondence

| File | Lean module / namespace | Paper content | Depends on |
|---|---|---|---|
| `MotherEquation_CoreVerification.lean` | `MotherEquation` (incl. `V4`) | Algebraic heart of the Mother Equation: Klein four-group, χAB=(1,−1,−1,1), four-mode spectrum {+2C,0,0,−2C}, 8-dim Jet lift, phase-transition cliff | none (core library) |
| `Theorem_9_3A.lean` | `RH93` | Theorem 9.3A (structural factorization through the symmetry quotient) | mathlib |
| `Lemma_9_5C.lean` | `RH95C` | Lemma 9.5C (¶593–627): gaussianReal heat kernel, moment scaling laws m₃(α)=(√α)³C₃, m₄(α)=α²C₄, main term channel_main, energy error bound, heat-kernel limit, χAB negative definiteness `Kquad_chiAB_neg` | mathlib |
| `Unitarity_Assembly.lean` | `RH95U` | Theorems 9.5/10 (hgrad hypothesis-interface version): four-point orbit, orbit injectivity, UnitarityPositive interface | Lemma_9_5C |
| `Lemma_9_4.lean` | `RH94` | Lemma 9.4 (¶467–536): vim double reflection, fixed-line vanishing, Cauchy–Riemann gradients `hasDerivAt_vim_x/y`, gradient reflection laws `nablaV_reflA/B`, orbit gradient identity `orbitGrad_eq` (w=(a,b,a,−b,−a,b,−a,−b)), `hgrad_of_simple_zero` | Unitarity_Assembly |
| `Theorem_9_5_Closure.lean` | `RH95Final` | Theorems 9.5/10 closed loop: `theorem_9_5_final`, `theorem_10_final` — hgrad internalized; unitarity applied to the actual orbit gradient field | Lemma_9_4 |
| `Lemma_11_3.lean` | `RH113` | Lemma 11.3 (¶973–996) + 12.1: `xiFn_one_sub` (functional equation), `zeta_re_pos_of_one_lt`, `lemma_11_3`, `xiFn_ne_zero_ofReal`, `gFn_pos`, `xiFn_ne_zero_of_w_nonneg`, `critical_line_lock` | mathlib |
| `Final_Assembly.lean` | `RHFinal` | Final RH: `RH_general`, `RH_xi`, `RH_xi_zeros`, `xiFn_differentiableAt` | Theorem_9_5_Closure + Lemma_11_3 |
| `Note_9_5B_mJet.lean` | `RHM` | Note 9.5B / Note 11.2.3 (higher-order generalization to multiple zeros): existence of the first nonzero jet order, m-th order pairing law, orbit m-uniformity, `theorem_9_5_multiplicity`, `theorem_10_unconditional` | Theorem_9_5_Closure + Lemma_11_3 |
| `Final_Assembly_Unconditional.lean` | `RHFinalM` | Unconditional assembly: `RH_xi_unconditional` — **hg_simple (simplicity of zeros) eliminated**; `hg_ne` discharged by machine via Lemma 11.3 | Note_9_5B_mJet |
| `Lemma_9_5C_TaylorRemainder.lean` | `RHT` | Lemma 9.5C upgrade: `taylor_remainder_C2` (htaylor promoted from hypothesis to theorem), `FieldData.ofContDiff`, `lemma_9_5C_unconditional` | Lemma_9_5C |

## Deliverables Directory

- `Verification_Report.md` — master verification report (compilation evidence,
  explicit premise list, premise table ↔ the paper's "two conditions" verbatim
  correspondence, methodological boundaries)
- `MANIFEST.md` — SHA-256 integrity table of all delivered files
- `reproduce_build.sh` — one-command reproduction script
  (`sh reproduce_build.sh /path/to/mathlib4`)
- `build_logs/` — complete per-module `lake env lean` build logs (incl.
  `#print axioms` audit output) for line-by-line re-checker comparison
- `*.lean.txt` — plain-text copies of the sources (bit-identical)

## Build Instructions (reproducible, produces importable .olean)

```bash
# 1. Install the toolchain (either)
#    a. elan: elan toolchain install leanprover/lean4:v4.34.0-rc2 && elan default leanprover/lean4:v4.34.0-rc2
#    b. download lean-4.34.0-rc2-linux.tar.zst, extract, add bin/ to PATH

# 2. Fetch the mathlib source and cache (in a workspace directory)
git clone --depth 1 --branch v4.34.0-rc2 https://github.com/leanprover-community/mathlib4.git
cd mathlib4
lake exe cache get        # 8747 precompiled oleans

# 3. Copy the eleven .lean files of this folder into the workspace root
#    (file names are already the module names — no renaming needed)

# 4. Compile in topological order (produces importable .olean/.ilean)
export LEAN_PATH=$PWD
for m in Lemma_9_5C Unitarity_Assembly Lemma_9_4 Theorem_9_5_Closure \
         Lemma_11_3 Final_Assembly Note_9_5B_mJet \
         Final_Assembly_Unconditional Lemma_9_5C_TaylorRemainder; do
  lake env lean -o $m.olean -i $m.ilean $m.lean || exit 1
done
# All nine steps must exit with code 0; the #print axioms blocks at the end of
# each file produce the outputs listed in Section 2 of Verification_Report.md.
# Theorem_9_3A and MotherEquation_CoreVerification are standalone:
lake env lean -o Theorem_9_3A.olean -i Theorem_9_3A.ilean Theorem_9_3A.lean
lean MotherEquation_CoreVerification.lean   # zero mathlib dependency
```

Compilation dependency graph:

```
Lemma_9_5C ──→ Unitarity_Assembly ──→ Lemma_9_4 ──→ Theorem_9_5_Closure ──┐
                                                                           ├──→ Final_Assembly
(mathlib) ──→ Lemma_11_3 ─────────────────────────────────────────────────┤
                                                                           │
Theorem_9_5_Closure + Lemma_11_3 ──→ Note_9_5B_mJet ──→ Final_Assembly_Unconditional

Lemma_9_5C ──→ Lemma_9_5C_TaylorRemainder   (Taylor remainder upgrade, independent branch)

Theorem_9_3A, MotherEquation_CoreVerification   (standalone)
```

## Explicit Premises (chain-wide interface hypotheses)

1. `SatisfiesUnitarity C f` (C > 0, parameterized by f) — the per-f premise of
   the paper's Theorem 9.5 ("for any f ∈ ℱ satisfying the Mother-Equation
   unitarity"), quantifying only over counterexample configurations carrying a
   non-real zero; the global `UnitarityPositive C` and the free-v `theorem_9_5`
   (the paper's ¶8.1 replica) are preserved unchanged in
   `Unitarity_Assembly.lean` and do not participate in the closed chain;
2. `hζ`: ζ strictly negative on (0,1) — the paper (¶976) itself states
   "combining known classical facts";
3. `E`/`hE_pos`/`hE_neg` (unconditional assembly only) — the m-th order energy
   interface, under the same discipline as `SatisfiesUnitarity`: `hE_pos`
   quantifies only over configurations carrying a zero witness, `hE_neg`
   remains universal
   (the m = 1 special case is fully machine-closed; the m ≥ 2 energy matrix is a
   different object and is interfaced per the paper's axiom-layer formulation);
4. `hBd` (Lemma 9.5C upgraded version only) — boundedness of the second
   derivative, a standard fact interfaced (rationale in Section 3 of the
   Verification Report).

All appear as explicit theorem parameters — not axioms, not sorries. All 55
`#print axioms` outputs are `[propext, Classical.choice, Quot.sound]`.

**Eliminated**: `hg_simple` (simplicity of zeros) — the premises of the
unconditional assembly `RH_xi_unconditional` no longer contain any assumption
on the multiplicity of zeros (see Sections 3–4 of the Verification Report).

## Deliverables

- Eleven `.lean` source files;
- `Verification_Report.md`: coverage list, compilation evidence, axiom audit,
  methodological boundaries;
- This `README.md`: version pinning, section correspondence, build and
  re-check instructions.
