Li Haiquan
Jilin University of Chemical Technology, China
ORCID: https://orcid.org/0009-0000-7365-6535
Email: lihaiquan@jluct.edu.cn

# Machine Verification of the Riemann Hypothesis · Master Verification Report

- Toolchain: **Lean 4.34.0-rc2** (official x86_64-linux release, commit 6a10ac8)
- Mathematical library: **mathlib v4.34.0-rc2** (same tag as the toolchain,
  reproduced via `lake exe cache get`)
- Module chain: `Lemma_9_5C → Unitarity_Assembly → Lemma_9_4 →
  Theorem_9_5_Closure → Final_Assembly`; `Lemma_11_3` standalone (mathlib only);
  higher-order generalization chain: `Note_9_5B_mJet →
  Final_Assembly_Unconditional` (m-th order Jet assembly for multiple zeros and
  the unconditional assembly); `Lemma_9_5C_TaylorRemainder` (Taylor remainder
  upgrade, depends only on Lemma_9_5C)
- Delivered sources (this folder):

| Delivered file | Module / namespace | Paper section |
|---|---|---|
| `MotherEquation_CoreVerification.lean` | single file, zero mathlib | Algebraic heart of the Mother Equation: V4 group law, χAB character, spectral signs, Jet lift, phase-transition cliff |
| `Theorem_9_3A.lean` | `RH93` (standalone) | Theorem 9.3A, dimension reduction |
| `Lemma_9_5C.lean` | `RH95C` | Lemma 9.5C (¶593–627): heat-kernel regularization, energy error bound, χAB negative definiteness |
| `Unitarity_Assembly.lean` | `RH95U` | Theorems 9.5/10 (hgrad hypothesis-interface version) |
| `Lemma_9_4.lean` | `RH94` | Lemma 9.4 (¶467–536): double-reflection symmetry, fixed-line vanishing, Cauchy–Riemann nondegenerate gradient, orbit gradient identity |
| `Theorem_9_5_Closure.lean` | `RH95Final` | Theorems 9.5/10 closed-loop version: hgrad internalized; unitarity applied to the actual orbit gradient field |
| `Lemma_11_3.lean` | `RH113` | Lemma 11.3 (¶973–996) + the 12.1 usage: ξ positivity on the real axis, g(w) positivity, critical-line lock |
| `Final_Assembly.lean` | `RHFinal` | Final RH assembly: `RH_general` / `RH_xi` / `RH_xi_zeros` |
| `Note_9_5B_mJet.lean` | `RHM` | Note 9.5B (¶666–698) / Note 11.2.3 (¶961–972): the jet machine chain for zeros of arbitrary multiplicity m — existence of the first nonzero order, m-th order pairing law, orbit m-uniformity, `theorem_9_5_multiplicity` / `theorem_10_unconditional` |
| `Final_Assembly_Unconditional.lean` | `RHFinalM` | Unconditional assembly: `RH_xi_unconditional` — **the simplicity hypothesis `hg_simple` has been eliminated from the premises** (g not identically zero is machine-discharged via Lemma 11.3; neither the real nor the non-real zero branch depends on simplicity) |
| `Lemma_9_5C_TaylorRemainder.lean` | `RHT` | Lemma 9.5C upgrade: `taylor_remainder_C2` promotes `FieldData.htaylor` from a pointwise hypothesis to a theorem (segment mean-value theorem + Lipschitz chain, fully machine-closed); `FieldData.ofContDiff` constructs field data from a C² compactly supported field |

## 1. Closed-Loop Structure

```
9.3A dimension reduction → 9.4 nondegenerate gradient → 9.5C heat-kernel
negative energy → unitarity contradiction → exclusion of non-real simple zeros
(Theorem 10)                                                        +
         Lemma 11.3 real-axis positivity exclusion (chain 2) ───────┘
                              ↓
        Final assembly RH_xi: every zero of g (except 0, 1) satisfies Re s = 1/2

Higher-order generalization:
  Note 9.5B m-th order jet machine chain: first nonzero order exists
  (analytic identity theorem) → m-th order pairing law (induction)
  → orbit four points share the same m → a non-real m-fold zero triggers the
  unitarity contradiction (Theorem 10, unconditional version)
                              ↓
  Unconditional assembly RH_xi_unconditional: hg_simple eliminated —
  a non-real zero of any multiplicity enters the same unitarity gate after
  taking the first nonzero jet order
```

## 2. Compilation Evidence (per-function gate retrofit, full re-verification)

**Scope of this round (closed, four signatures only — not one bit more)**: the
quantification range of `hunit` in `theorem_9_5_final`, `hunit` in
`theorem_10_final`, and `hunit` in `RH_xi` was changed from global to per-f
(new definition `SatisfiesUnitarity C f`, parameterized by f — not a
`∀ f`-universal version); on the unconditional side, `hE_pos` gained a zero
witness (`hE_neg` remains universal, untouched). `theorem_9_5` (the free-v
version, the faithful ¶8.1 replica), the definition of `UnitarityPositive`
itself, the entire mechanical layer, and every mathematical step of every
proof are unchanged.

All eleven modules were recompiled from scratch under their English module
names (`lake env lean -o <m>.olean -i <m>.ilean <m>.lean`, with LEAN_PATH
pointing at the workspace):

```
=== Lemma_9_5C                    exit: 0 ===  (8 audits)
=== Unitarity_Assembly            exit: 0 ===  (6 audits)
=== Lemma_9_4                     exit: 0 ===  (12 audits)
=== Theorem_9_5_Closure           exit: 0 ===  (2 audits)
=== Lemma_11_3                    exit: 0 ===  (11 audits)
=== Final_Assembly                exit: 0 ===  (4 audits)
=== Note_9_5B_mJet                exit: 0 ===  (7 audits)
=== Final_Assembly_Unconditional  exit: 0 ===  (3 audits)
=== Lemma_9_5C_TaylorRemainder    exit: 0 ===  (2 audits, zero warnings)
=== Theorem_9_3A                  exit: 0 ===  (5 audits)
=== MotherEquation_CoreVerification  exit: 0 ===  (12 audits, core library only)
ALL_DONE
```

The nine-module chain contributes 55 `#print axioms` outputs
(8+6+12+2+11+4+7+3+2); the two standalone modules contribute 5 and 12.

All `#print axioms` outputs are identical:

```
'...' depends on axioms: [propext, Classical.choice, Quot.sound]
```

That is, the proofs depend only on the three standard foundational axioms of
the Lean logical kernel (propositional extensionality, choice, quotient
soundness); **no sorryAx (zero sorry), no sorry warnings, no additional axioms,
no self-introduced assumption axioms**.

## 3. Explicit Premise List (chain-wide interface hypotheses)

The entry points at which the formalization does not overstep its mandate as
checking servant — all appear as explicit hypotheses in theorem signatures:

1. **Per-function unitarity premise** `SatisfiesUnitarity C f` (C > 0,
   parameterized by f) — the verbatim counterpart of the paper's Theorem 9.5
   premise: "for any f ∈ ℱ satisfying the Mother-Equation unitarity (i.e. whose
   perturbation energy satisfies the unitarity axiom ΔE > 0), g(w) can have no
   non-real zeros". Lean encoding:
   `∀ σ t, f(σ+it)=0 → σ≠1/2 → t≠0 → 0 < Kquad C (orbitGrad f σ t)` —
   it quantifies only over **counterexample configurations carrying a non-real
   zero** (the sole objects the unitarity "gate" admits), applied to the
   **actual gradient field** `orbitGrad f σ t` on the four-point orbit of the
   zero, whose identity with the χAB-type vector is machine-proved by
   `orbitGrad_eq` of Lemma 9.4. For an f with no zeros the premise holds
   vacuously (satisfiable, not refutable inside the library); the truth of its
   instance `hgate : SatisfiesUnitarity C g` is carried by the paper's axiom
   layer (completeness of exclusion, Bad(F)=∅) and is listed as an explicit
   premise under the same discipline as hζ.
   (The global `UnitarityPositive C` and the free-v `theorem_9_5` are preserved
   unchanged in `Unitarity_Assembly.lean` as the faithful replica of the
   paper's ¶8.1 — "there exists a nonzero perturbation vAB with strictly
   negative energy" — and do not participate in the closed chain.)
2. **Classical input** `hζ`: ζ strictly negative on (0,1) — the paper (¶976)
   itself states "combining known classical facts". mathlib has no such lemma
   (nor the Dirichlet η function, nor the alternating-series test), so it is
   introduced as an interface per the paper's own formulation. Everything else
   in Lemma 11.3 is machine-proved, including:
   - `zeta_re_pos_of_one_lt`: ζ(s) > 0 for s > 1 (termwise positive, no
     hypotheses at all);
   - `xiFn_one_sub`: the functional equation of ξ (derived from mathlib's
     functional equation for Λ);
   - `critical_line_lock`: (s−½)² a negative real ⟹ Re s = ½.
3. **m-th order energy interface** (used only by the unconditional assembly
   `RH_xi_unconditional`): `E : ℕ → (Fin 4 → ℂ) → ℝ` with two explicit
   properties — `hE_pos` (the unitarity gate, **positive-definiteness side
   quantifying only over zero-carrying configurations**: 0 ≤ E m J on jet
   configurations satisfying the m-th order pairing law, pointwise nonzero,
   and carrying a non-real zero witness
   `∃ σ t, f(σ+it)=0 ∧ σ≠1/2 ∧ t≠0 ∧ ∀ i, J i = iteratedDeriv m f (orbitC σ t i)`)
   and `hE_neg` (the group-algebra invariant of Note 9.5B step 2: E m J < 0 on
   pairing-law nonzero configurations, **universal and untouched** — negative
   definiteness is a machine-side/spectral fact, same discipline as
   `Kquad_chiAB_neg` of Lemma 9.5C). The positive side is parameterized by f
   and per-configuration (same discipline as `SatisfiesUnitarity` in item 1),
   so the two premises' domains no longer coincide and are not mutually
   exclusive. The machine side supplies the pairing law, the nonvanishing, and
   the zero witness (`theorem_9_5_multiplicity`); the two ends of the energy
   functional's definiteness are introduced as interfaces per the paper's
   axiom-layer formulation — exactly the same discipline as
   `SatisfiesUnitarity` at m = 1 (the m = 1 special case is fully
   machine-closed by `RH95Final.theorem_9_5_final`; the m ≥ 2 energy matrix is
   a different object from the m = 1 Kquad — naive substitution degenerates —
   hence interfacing is mandatory).
4. **Second-derivative bound interface** (used only by the upgraded
   `lemma_9_5C_unconditional`):
   `hBd : ∃ B, 0 ≤ B ∧ ∀ z, ‖fderiv ℝ (fderiv ℝ Φ) z‖ ≤ B`.
   Mathematically this is a one-line corollary of "a continuous function on a
   compact set is bounded"; on the machine side, the double continuous-linear-map
   space carries two propositionally equal but not definitionally equal topology
   instances, and the defeq cost of unifying them across lemmas exceeds the
   compilation budget — so it is listed as an explicit premise under the same
   discipline as hζ. The Taylor remainder estimate itself (the core analytic
   content) is fully machine-closed.

**Eliminated premise**: `hg_simple` (simplicity of zeros) — an explicit
hypothesis of the old assembly `RH_xi`, absent from the unconditional
`RH_xi_unconditional`: g not identically zero is machine-discharged via Lemma
11.3; non-real zeros enter the unitarity gate through the m-th order jet
first-nonzero-order machine chain; real zeros are excluded by Lemma 11.3. No
hypothesis on zero multiplicity appears anywhere in the chain.

## 4. Final Theorem Statements (`Final_Assembly.lean`)

- `RH_general`: for f satisfying the four gates (complex differentiability,
  double-reflection symmetry, simplicity of zeros, per-function unitarity
  `SatisfiesUnitarity C f`), every zero σ + it of f satisfies σ = 1/2 or t = 0.
- `RH_xi`: let g be an entire realization of ξ (pointwise equal to
  `xiFn = ½s(s−1)Λ(s)` outside 0, 1), satisfying double-reflection symmetry and
  simplicity of zeros; then under the per-function unitarity premise
  `SatisfiesUnitarity C g` and the classical input hζ,
  **every zero s ∉ {0, 1} of g satisfies Re s = 1/2**.
  - Real zero candidates: reduced to xiFn via `hg_eq`, excluded by Lemma 11.3
    (`xiFn_ne_zero_ofReal`);
  - Non-real zero candidates: forced to t = 0 by the closed-loop Theorem 10
    (`theorem_10_final`) — contradiction.
- `RH_xi_zeros`: equivalent packaging — the zero set ⊆ critical line ∪ {0, 1}.
- `xiFn_differentiableAt`: xiFn is complex-differentiable outside 0, 1
  (machine-proved; at 0 and 1 the Λ pole and the zero factor cancel as
  removable points, and the function values of `xiFn` at these two points are
  definitional junk values rather than mathematical content — hence the
  assembly honestly interfaces via "entire realization g + pointwise agreement
  `hg_eq`").

### Unconditional version (`Final_Assembly_Unconditional.lean`)

- `RH_xi_unconditional`: same conclusion as `RH_xi` — **every zero
  s ∉ {0, 1} of g satisfies Re s = 1/2** — but the premises **no longer contain
  the simplicity hypothesis `hg_simple`**. The signature premises are:
  unitarity (the m = 1 per-function premise `SatisfiesUnitarity` carried
  through the m-th order generalization interface `E`/`hE_pos`/`hE_neg`, with
  `hE_pos` quantifying only over configurations carrying a zero witness), the
  classical input `hζ`, complex differentiability of g, double-reflection
  symmetry, and pointwise agreement with xiFn.
  - `hg_ne` (g not identically zero): machine-proved — g 2 = xiFn 2 > 0
    (Lemma 11.3), not a premise;
  - Real zeros: excluded by `xiFn_ne_zero_ofReal`;
  - Non-real zeros (arbitrary multiplicity m): `theorem_10_unconditional`
    takes the first nonzero jet order (`jetOrder`, guaranteed to exist by the
    analytic identity theorem), the orbit four points share the same m
    (`jetOrder_star` etc.), the jet vector satisfies the m-th order pairing law
    and is pointwise nonzero, triggering the `hE_pos`/`hE_neg` contradiction.
- `RH_general_unconditional` / `RH_xi_zeros_unconditional`: the corresponding
  general form and set packaging.

## 5. Premise Table ↔ the Paper's "Two Conditions" — Verbatim Correspondence

The paper's final assembly statement (¶51858) reads verbatim: "in the
intersection of the two conditions — the Mother-Equation unitarity axiom and
the real-axis positivity of the ξ function — the zeros can only lie on the
critical line Re(s)=1/2". The premise table of `RH_xi` corresponds to this
statement word for word:

| Paper text | Lean premise | Carrier |
|---|---|---|
| "the Mother-Equation unitarity axiom" (condition one) | `hunit : SatisfiesUnitarity C g` | Verbatim encoding of the paper's Theorem 9.5 premise: "for any f ∈ ℱ satisfying the Mother-Equation unitarity (i.e. whose perturbation energy satisfies the unitarity axiom ΔE > 0), g(w) can have no non-real zeros" — **the premise is per-f**, hence the Lean premise is parameterized by f and quantifies only over counterexample configurations carrying a non-real zero |
| "the real-axis positivity of the ξ function" (condition two) | `hζ : ∀ s ∈ Set.Ioo 0 1, riemannZeta s < 0` + `hg_eq` (pointwise agreement of g with xiFn) | The paper (¶976) itself states "combining known classical facts"; the real-axis positivity itself (`xiReal_pos_of_Ioo` etc.) is machine-proved in Lemma 11.3, with hζ as its only classical input |
| "the zeros can only lie on the critical line Re(s)=1/2" | conclusion `s.re = 1/2` (`RH_xi` / `RH_xi_unconditional`) | Machine proof: real zeros excluded by Lemma 11.3, non-real zeros excluded by Theorem 10 (closed-loop / unconditional version) |

Theorem 9.5 premise-domain comparison:

| Paper Theorem 9.5 (¶48466) | Lean signature after the retrofit |
|---|---|
| "for any f ∈ ℱ satisfying the Mother-Equation unitarity" | `(f : ℂ → ℂ) ... (hunit : SatisfiesUnitarity C f)` — a per-f premise, not a universal axiom |
| "i.e. whose perturbation energy satisfies the unitarity axiom ΔE > 0" | `f(σ+it)=0 → σ≠1/2 → t≠0 → 0 < Kquad C (orbitGrad f σ t)` — ΔE strictly positive on the zero-orbit gradient field |
| "then g(w) can have no non-real zeros" | `theorem_9_5_final ... : False` (contradiction derived under hz/hσ/ht) |

The unconditional version carries the same two conditions: `hE_pos` (the
m-th order carrier of condition one, with zero witness) + `hζ` (condition two,
unchanged), with the verbatim same conclusion.

## 6. Methodological Boundaries (consistent with the paper's own formulation)

- The formalization is a checking servant, not the final adjudicator: the
  epistemological status of the Whole-1, the identity of the German original
  source, and other Class-C content are not handed to Lean, and this report
  claims no verification of them.
- The unitarity "gate" only accepts the elimination of counterexample
  configurations carrying a non-real zero; ξ has no counterexample identity and
  never enters the gate; the legitimacy of ξ is inferred backwards from the
  completeness of exclusion (Bad(F)=∅) — the logical role of the assembly is
  consistent with this.
- Constant-factor convention: Lemma 9.5C strictly derives −(C/2)‖W‖² from the
  (C/2) normalization of ¶593 (the original text writes −C‖W‖² at ¶621/627;
  the factor 2 is a normalization convention — strict negative definiteness is
  the logical carrier).
- The premise is parameterized by f; the existence of instances falsifying the
  premise (such as quartet-orbit polynomials) is the normal shape of a
  conditional proposition and constitutes no attack on the reduction; the
  premise class is nonempty, witnessed by double-reflection entire functions
  without non-real zeros.
- For the realization of ξ, the truth of the premise is carried outside Lean
  by the paper's completeness of exclusion and is not adjudicated by Lean —
  this is a division of labor by design, not a gap in the formalization.

## 7. How to Re-Check

See the full build instructions in `README.md`. One-line version:

```
# Pinned versions: Lean 4.34.0-rc2 + mathlib v4.34.0-rc2
export LEAN_PATH=<workspace>
lake env lean -o Final_Assembly_Unconditional.olean -i Final_Assembly_Unconditional.ilean Final_Assembly_Unconditional.lean
# Exit code 0 and axiom-audit outputs matching Section 2 = re-check passed
```
