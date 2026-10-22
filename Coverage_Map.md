Li Haiquan
Jilin University of Chemical Technology, China
ORCID: https://orcid.org/0009-0000-7365-6535
Email: lihaiquan@jluct.edu.cn

# Coverage Map

Paper: *A Successful Mathematical Derivation of the Riemann Hypothesis via Bidirectional Forward-Reverse Closure* (V2, 70 pages).
Lean package: the twelve modules listed in `MANIFEST.md`.

Lean locks the load-bearing skeleton. It does not translate the paper sentence by sentence. A page of history, motivation, physical picture, or repeated emphasis is not a second proof obligation. A step that changes a theorem, and that the closure actually uses, is.

This file does not say that the twelve modules prove the Riemann Hypothesis. It says which V2 statements those modules lock, which statements stay explicit premises, and which passages are not machine obligations.

## 1. What “enough” means here

The closure uses this chain:

German original, as the proposition and the object ξ
→ Mother Equation, as the paper’s Whole 1, including the unitarity constitution
→ Theorem 9.3A and the zero classification
→ Theorem 9.4, the χAB germ
→ the spectral sign on that germ (Parts 1–8, Lemma 9.5A, Lemma 9.5C)
→ Theorem 9.5 / Theorem 10, exclusion of a nonreal zero
→ Note 9.5B / Note 11.2.3, arbitrary multiplicity
→ Lemma 11.3, real-axis positivity to the critical line
→ Theorems 12.1 and 12.2, the assembly

Sections 5A.8 and 5A.9 name the second-gate criterion. They are not steps inside the deduction of Theorem 9.5 or Theorem 12.1. V2 says so: Section 5A does not enter the later closure.

## 2. Explicit premises

These are not missing modules. Each one is a hypothesis of a theorem that does compile. The paper’s own reading of the unitarity constitution is recorded in `Verification_Report.md`: for ξ, that constitution is carried by the paper and is not re-adjudicated inside Lean.

| Premise in Lean | Paper status | Where it sits |
|---|---|---|
| `hSpec : Set.range α = Z` | Premise P1 of Section 5A. P1a–P1b are the spectral reading. V2 does not derive P1 from the German wording inside the closure. | `Section5A8_Unitarity.lean` |
| `SatisfiesUnitarity C f` | The per-function form of the Mother Equation constitution ΔE > 0, applied only to a configuration that carries a nonreal zero. | `Theorem_9_5_Closure.lean`, `Final_Assembly.lean` |
| `hE_pos`, `hE_neg` | The same constitution at jet order m. The sign for m = 1 is the theorem `Kquad_chiAB_neg`. The m ≥ 2 energy matrix remains the interface `hE_neg`. | `Note_9_5B_mJet.lean`, `Final_Assembly_Unconditional.lean` |
| `hζ` | V2’s “known fact” that ξ is strictly positive on (0, 1), introduced as the classical input of Lemma 11.3. | `Lemma_11_3.lean`, both assemblies |
| `hBd` | Boundedness of the second derivative for a C² compactly supported field. V2 treats this as part of Φ ∈ C_c^∞. | `Lemma_9_5C_TaylorRemainder.lean` |

`Final_Assembly.lean` still has the simplicity hypothesis `hg_simple`. `Final_Assembly_Unconditional.lean` removes it and uses the jet-order interface above.

## 3. Section table

| V2 location | Class | Lean home |
|---|---|---|
| Abstract; Special Emphases 1–5 | Reading of the method. No separate calculation. | None. Not a machine obligation. |
| Section 1. German original and the definition of ξ | The proposition and the object. Entireness, reality, evenness, and the multiplier-free equation are the memoir’s definition of ξ. | None. This is the proposition, not a lemma waiting for a file. |
| Section 2. Zero correspondence of ξ and ζ; ξ ∈ F, ζ ∉ F | Comparison. The closure never uses a ζ-side bridge. ξ ∈ F is the object named in Section 1. | None. The package does not formalize the ζ correspondence. |
| Section 3. Functional equation to V₄ | The group law used later. | `MotherEquation_CoreVerification.lean` (Klein four-group, characters, orbit). Reflections of a point: `Unitarity_Assembly.lean`, `Lemma_9_4.lean`. |
| Sections 4–6, except the two rows below | Legitimacy, physical genes, “no external bridge.” | None. Narrative. |
| 5A.1–5A.7, 5A.10, 5A.11 | Layering, notation, the six genes, Gate 1 restated, V₄ on the zero set, geometric birth of 1/2, declaration of P1, non-externality. | The geometric reflections and V₄ are the modules in the Section 3 row. P1 is the premise `hSpec`, not a derived theorem. |
| 5A.8 | Load-bearing for the criterion only: under P1, five statements are equivalent. | `Section5A8_Unitarity.lean`, theorem `five_eight_equiv`. The Lean proof is the diagonal eigen-direction form of that equivalence. It does not rebuild deficiency indices, and it does not prove that the roots are real. |
| 5A.9 | Mathematical argument that, under P1 and the conservation conditions A1–A4, the guard’s form is self-adjointness / unitarity / real conserved energy. V2 does not use 5A.9 as a step of Theorem 9.5 or Theorem 12.1. | No module. Recorded here so it is not mistaken for a hidden step of the closure. |
| Part 1, 1.2–1.3. Definition of the kernel and the unitarity constitution | Definition of Whole 1. | The constitution is the premise in Section 2 of this file. The kernel’s spectral calculation is the next row. |
| Parts 2–3. Axes, intersection, orbit dimension | Geometry of the two reflections and of the stabilizer. | `Unitarity_Assembly.lean` (`orbit`, `orbit` distinctness). Unique stable output of the spectrum: `MotherEquation_CoreVerification.lean` (`phase_cliff`). |
| Parts 4–8 and 9.2. Matrix entries, V₄ modes, hand computation of ⟨v_AB, Kv_AB⟩, sign, phase transition | One spectral certificate, written out element by element. | `MotherEquation_CoreVerification.lean`: `gK_eig_chiAB`, `spectrum_complete`, `energy_expansion`, `chiAB_pure_energy_negative`, `collapse_stable`, `jet_eigenvalue`, `jet_energy`, `jet_negative`, `phase_cliff`, `mother_equation_core_certificate`. Lean uses the doubled normalization (−2C, −2C+2ε). V2’s −C is the same strict negativity; the factor is the convention already stated in `Verification_Report.md`. |
| 9.1, Theorem 9.1.2. V₄ from double reflection | Group law. | `MotherEquation_CoreVerification.lean`. |
| Theorem 9.3A; Corollary 9.3B; Theorem 11.1.1; Corollary 11.1.2 | Load-bearing. Dimension reduction and the three zero shapes. | `Theorem_9_3A.lean`: `theorem_9_3A`, `unique_rep`, real coefficients. The shapes are the representation f(s) = g((s−1/2)²) used by both assemblies. |
| Theorem 9.4 | Load-bearing. χAB germ, Cauchy–Riemann gradient, orbit gradient. | `Lemma_9_4.lean`. |
| Lemma 9.5A | Load-bearing content: the jet of a simple zero inherits the χAB eigenvalue. | Integer jet certificate: `MotherEquation_CoreVerification.lean` (`jet_*`). Analytic quadratic form and the negative sign: `Lemma_9_5C.lean` (`Kquad_chiAB_neg`). |
| Lemma 9.5C | Load-bearing. Heat-kernel limit and remainder. | `Lemma_9_5C.lean`. The C² remainder estimate: `Lemma_9_5C_TaylorRemainder.lean` under `hBd`. |
| Theorem 9.5, Steps 1–7; Theorem 10 | Load-bearing. A nonreal zero produces negative energy and contradicts the constitution. | `Theorem_9_5_Closure.lean` (`theorem_9_5_final`, `theorem_10_final`) under `SatisfiesUnitarity`. The free-v replica of ¶8.1 is `Unitarity_Assembly.lean` (`theorem_9_5`, `theorem_10`) under `UnitarityPositive`. |
| Theorem 9.5, Step 8; Lemma 11.3; the critical-line lock | Load-bearing once the classical positivity input is granted. | `Lemma_11_3.lean` under `hζ`. |
| Note 9.5B; Note 11.2.3 | Load-bearing for a zero of multiplicity m ≥ 1. | `Note_9_5B_mJet.lean`. Existence of the first nonzero order, the pairing laws, and orbit uniformity are theorems. The m-th energy sign is `hE_pos` / `hE_neg`; m = 1 is `Kquad_chiAB_neg`. |
| Part 10. Theorems 10.1.3, 10.2.2, 10.2.4, 10.2.5, 10.3.2 | Same geometry and the same spectral cliff as Parts 2–8, rewritten as the forward scan. | `MotherEquation_CoreVerification.lean` (`phase_cliff`, `collapse_stable`, `no_intermediate_state`) and `Unitarity_Assembly.lean`. |
| Theorems 11.2.1, 11.2.2 | Forward restatement of Theorem 9.5. | `Theorem_9_5_Closure.lean` and `Final_Assembly*.lean`. |
| Theorem 12.1; Theorem 12.2 | Load-bearing assembly. | `Final_Assembly.lean` (`RH_xi`, with `hg_simple`) and `Final_Assembly_Unconditional.lean` (`RH_xi_unconditional`, simplicity removed, jet interface retained). |
| 12.3–12.6, Discussion, Conclusion | Status of the result, including V2’s statement that the result is not a formalized proof. | None. |

## 4. Sentence for publication

The twelve Lean modules lock the load-bearing closure of V2: dimension reduction, the χAB germ, the spectral sign, exclusion of a nonreal zero, the passage from real-axis positivity to the critical line, and the assembly. Section 5A.8’s five-way equivalence is locked under `hSpec`. The German original is the proposition. Section 5A.9 is a prose argument about the form of the guard and is not a step of that closure. The premises in Section 2 of this file stay on the theorem signatures.
