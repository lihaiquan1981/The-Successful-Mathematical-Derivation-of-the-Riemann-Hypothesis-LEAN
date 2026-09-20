/-
Li Haiquan
Jilin University of Chemical Technology, China
ORCID: https://orcid.org/0009-0000-7365-6535
Email: lihaiquan@jluct.edu.cn
-/

import Lemma_9_4

/-!
# Theorem 9.5 / Theorem 10 — Unitarity Final Review (Closed-Loop Version)

Difference from `Unitarity_Assembly.lean`: `hgrad` is no longer a hypothesis
interface — it is proved internally from Lemma 9.4(c)
(`RH94.hgrad_of_simple_zero` / `RH94.nablaV_ne_zero`); and the vector to which
the unitarity condition is applied is not the abstract chiABVec, but the
**actual gradient field** `orbitGrad f σ t` on the four-point orbit of the zero.
Their identity is given by Lemma 9.4's `orbitGrad_eq`
(w = (a,b,a,−b,−a,b,−a,−b)).

Closed chain (all machine-verified):
  non-real simple zero ρ = σ + it (σ ≠ 1/2, t ≠ 0, f′(ρ) ≠ 0)
  → four-point orbit orbit σ t (four distinct points, `orbit_injective`)
  → orbit gradient field W = orbitGrad f σ t = chiABVec(∇v(ρ)) (9.4, `orbitGrad_eq`)
  → ∇v(ρ) ≠ 0 (9.4(c), `nablaV_ne_zero`) ⇒ W ≠ 0
  → 9.5C: ⟨W, K̃W⟩ = −(C/2)‖W‖² < 0 (`Kquad_chiAB_neg`)
  → contradicts the per-function unitarity premise (`SatisfiesUnitarity C f`)
  ⇒ the counterexample configuration carrying a non-real zero is rejected
    at the gate.

Hypothesis list (all explicit):
  · f is ℂ-differentiable;
  · double-reflection symmetry f(1−s) = f(s), f(s̄) = conj(f(s));
  · simplicity of zeros: f(ρ) = 0 ⇒ f′(ρ) ≠ 0 (for non-real zeros with σ ≠ 1/2);
  · the **per-function unitarity premise** `SatisfiesUnitarity C f` — exactly
    the premise of the paper's Theorem 9.5: "for any f ∈ ℱ satisfying
    mother-equation unitarity (i.e. whose perturbation energy satisfies the
    unitarity axiom ΔE > 0), g(w) has no non-real zeros". The gate adjudicates
    only configurations actually induced by zeros of this f; it is NOT the
    universal statement over all pairing-law vectors (that universal statement
    is the object of the paper's Part 8 intrinsic contradiction, kept in
    `Unitarity_Assembly.lean` as `UnitarityPositive`, and is not used as a
    premise anywhere in this chain).
-/

open RH95C RH95U RH94

namespace RH95Final

/-- **SatisfiesUnitarity C f** — the per-function unitarity premise of the
paper's Theorem 9.5: every gradient configuration actually induced by a
non-real zero of f has strictly positive energy.
Parameterized by the specific f (a universal `∀ f` version would be refutable
inside the library — e.g. f(s) = (s−1/2)² + a² is a double-reflection entire
function with the non-real zeros 1/2 ± ia). For f without non-real zeros it
holds vacuously; its truth for the ξ-realization g is carried by the paper's
axiom layer (exclusion completeness, Bad(F) = ∅), outside Lean's mandate —
the same discipline as `hζ`. -/
def SatisfiesUnitarity (C : ℝ) (f : ℂ → ℂ) : Prop :=
  ∀ σ t : ℝ, f (↑σ + Complex.I * ↑t) = 0 → σ ≠ 1 / 2 → t ≠ 0 →
    0 < Kquad C (orbitGrad f σ t)

/-- **Theorem 9.5 (Unitarity final review, closed loop)**:
    the counterexample configuration of a non-real simple zero self-destructs
    at the unitarity gate. -/
theorem theorem_9_5_final (C : ℝ) (hC : 0 < C)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f (1 - s) = f s) (h_conj : ∀ s, f (star s) = star (f s))
    (hsimple : ∀ σ t : ℝ, f (↑σ + Complex.I * ↑t) = 0 →
      deriv f (↑σ + Complex.I * ↑t) ≠ 0)
    (hunit : SatisfiesUnitarity C f)
    {σ t : ℝ} (hz : f (↑σ + Complex.I * ↑t) = 0) (hσ : σ ≠ 1/2) (ht : t ≠ 0) :
    False := by
  -- Non-real zero ⇒ orbit of four distinct points (non-degeneracy of the
  -- configuration admitted at the gate)
  have hdistinct : Function.Injective (orbit σ t) := orbit_injective hσ ht
  -- 9.4(c): ∇v(ρ) ≠ 0
  have e : (↑σ + ↑t * Complex.I : ℂ) = ↑σ + Complex.I * ↑t := by rw [mul_comm]
  have hv : nablaV f (σ, t) ≠ 0 := nablaV_ne_zero hf (by rw [e]; exact hsimple σ t hz)
  -- 9.4 orbit gradient field = χAB-type vector
  have hW : orbitGrad f σ t = chiABVec (nablaV f (σ, t)) := orbitGrad_eq hf h_sym h_conj σ t
  have hA : ∀ i, chiABVec (nablaV f (σ, t)) (iA i) = JB (chiABVec (nablaV f (σ, t)) i) :=
    chiABVec_A _
  have hB : ∀ i, chiABVec (nablaV f (σ, t)) (iB i) = JA (chiABVec (nablaV f (σ, t)) i) :=
    chiABVec_B _
  have hne : ∃ i, chiABVec (nablaV f (σ, t)) i ≠ 0 := chiABVec_nonzero hv
  -- The unitarity gate requires positive energy of the actual zero-induced
  -- orbit gradient field (the per-function premise of the paper's Theorem 9.5)
  have hpos : 0 < Kquad C (orbitGrad f σ t) := hunit σ t hz hσ ht
  -- 9.5C: energy is strictly negative on χAB-type nonzero configurations
  have hneg : Kquad C (orbitGrad f σ t) < 0 := by
    rw [hW]
    exact Kquad_chiAB_neg C _ hC hA hB hne
  linarith

/-- **Theorem 10 (zero exclusion, closed loop)**:
    under the explicit hypothesis list, any zero σ + it of f with σ ≠ 1/2
    must have t = 0. -/
theorem theorem_10_final (C : ℝ) (hC : 0 < C)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f (1 - s) = f s) (h_conj : ∀ s, f (star s) = star (f s))
    (hsimple : ∀ σ t : ℝ, f (↑σ + Complex.I * ↑t) = 0 →
      deriv f (↑σ + Complex.I * ↑t) ≠ 0)
    (hunit : SatisfiesUnitarity C f) :
    ∀ σ t : ℝ, f (↑σ + Complex.I * ↑t) = 0 → σ ≠ 1/2 → t = 0 := by
  intro σ t hz hσ
  by_contra ht
  exact theorem_9_5_final C hC f hf h_sym h_conj hsimple hunit hz hσ ht

end RH95Final

/- ## Axiom audit -/
section Audit
#print axioms RH95Final.theorem_9_5_final
#print axioms RH95Final.theorem_10_final
end Audit
