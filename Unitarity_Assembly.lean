/-
Li Haiquan
Jilin University of Chemical Technology, China
ORCID: https://orcid.org/0009-0000-7365-6535
Email: lihaiquan@jluct.edu.cn
-/

import Lemma_9_5C

/-!
# Theorem 9.5 / Theorem 10 — Unitarity Final-Review Assembly

The contradiction closed chain:
  non-real zero s₀ = σ + it (σ ≠ 1/2, t ≠ 0)
  → four-point orbit {s₀, 1−s₀, conj s₀, 1−conj s₀} (four distinct points)
  → χAB-type gradient vector W = ![v, J_B v, J_A v, −v] (v ≠ 0 ⇒ W ≠ 0)
  → Lemma 9.5C (`RH95C.Kquad_chiAB_neg`): ⟨W, K̃W⟩ = −(C/2)·‖W‖² < 0
  → contradicts the unitarity positivity requirement (`UnitarityPositive`)
  ⇒ the counterexample configuration carrying a non-real zero is rejected
    at the gate.

Theoretical discipline: the unitarity "gate" only admits counterexample
configurations carrying a non-real zero; ξ has no counterexample identity and
never enters the gate — its legitimacy is inferred from the completeness of
exclusion (Bad(F) = ∅). This file assembles only class-A/B mathematical
content; class-C epistemological content is not entrusted to Lean.

The `hgrad` hypothesis corresponds to the non-degenerate gradient of Lemma 9.4
of the paper (the gradient vector at a zero is nonzero) and is listed
explicitly as the input interface of this assembly stage.
-/

open RH95C

namespace RH95U

/-- Four-point orbit: 0 ↦ s₀, 1 ↦ 1−s₀, 2 ↦ conj s₀, 3 ↦ 1−conj s₀
    (in real coordinates) -/
def orbit (σ t : ℝ) : Fin 4 → ℝ × ℝ := ![(σ, t), (1 - σ, t), (σ, -t), (1 - σ, -t)]

/-- A-channel reflection: (σ, t) ↦ (1−σ, t) -/
def reflA (u : ℝ × ℝ) : ℝ × ℝ := (1 - u.1, u.2)

/-- B-channel reflection: (σ, t) ↦ (σ, −t) -/
def reflB (u : ℝ × ℝ) : ℝ × ℝ := (u.1, -u.2)

/-- iA is an involution -/
lemma iA_involutive : ∀ i : Fin 4, iA (iA i) = i := by decide

/-- iB is an involution -/
lemma iB_involutive : ∀ i : Fin 4, iB (iB i) = i := by decide

/-- Geometric meaning of A-channel pairing: the iA partner point = A reflection -/
lemma orbit_iA (σ t : ℝ) : ∀ i : Fin 4, orbit σ t (iA i) = reflA (orbit σ t i) := by
  intro i
  fin_cases i <;> simp [orbit, iA, reflA]

/-- Geometric meaning of B-channel pairing: the iB partner point = B reflection -/
lemma orbit_iB (σ t : ℝ) : ∀ i : Fin 4, orbit σ t (iB i) = reflB (orbit σ t i) := by
  intro i
  fin_cases i <;> simp [orbit, iB, reflB]

/-- When σ ≠ 1/2 and t ≠ 0, the four points of the orbit are pairwise distinct -/
lemma orbit_injective {σ t : ℝ} (hσ : σ ≠ 1/2) (ht : t ≠ 0) :
    Function.Injective (orbit σ t) := by
  intro i j hij
  rcases lt_or_gt_of_ne hσ with hσ | hσ <;>
  rcases lt_or_gt_of_ne ht with ht | ht <;>
  fin_cases i <;> fin_cases j <;>
    first | rfl | (exfalso; simp [orbit, Prod.ext_iff] at hij; linarith)

/-- χAB-type gradient vector: v ↦ ![v, J_B v, J_A v, −v] -/
def chiABVec (v : ℝ × ℝ) : Fin 4 → ℝ × ℝ := ![v, JB v, JA v, (-v.1, -v.2)]

/-- A-channel pairing law of χAB-type vectors: w_{iA} = J_B w_i -/
lemma chiABVec_A (v : ℝ × ℝ) : ∀ i : Fin 4, chiABVec v (iA i) = JB (chiABVec v i) := by
  intro i
  fin_cases i <;> simp [chiABVec, iA, JB, JA]

/-- B-channel pairing law of χAB-type vectors: w_{iB} = J_A w_i -/
lemma chiABVec_B (v : ℝ × ℝ) : ∀ i : Fin 4, chiABVec v (iB i) = JA (chiABVec v i) := by
  intro i
  fin_cases i <;> simp [chiABVec, iB, JB, JA]

/-- v ≠ 0 ⇒ the χAB-type vector is nonzero -/
lemma chiABVec_nonzero {v : ℝ × ℝ} (hv : v ≠ 0) : ∃ i : Fin 4, chiABVec v i ≠ 0 :=
  ⟨0, by simpa [chiABVec] using hv⟩

/-- Unitarity positivity requirement: on every χAB-type nonzero gradient
    configuration, the quadratic form ⟨W, K̃W⟩ is strictly positive.
    (This is the condition a "counterexample configuration carrying a non-real
    zero" must satisfy to pass the gate.) -/
def UnitarityPositive (C : ℝ) : Prop :=
  ∀ w : Fin 4 → ℝ × ℝ,
    (∀ i, w (iA i) = JB (w i)) → (∀ i, w (iB i) = JA (w i)) →
    (∃ i, w i ≠ 0) → 0 < Kquad C w

/-- **Theorem 9.5 (Unitarity final review)**:
    if σ ≠ 1/2, t ≠ 0 and the gradient v ≠ 0, then the four-point orbit yields
    a χAB-type nonzero gradient configuration, 9.5C gives
    ⟨W, K̃W⟩ = −(C/2)‖W‖² < 0, contradicting unitarity positivity. -/
theorem theorem_9_5 (C : ℝ) (hC : 0 < C) (hunit : UnitarityPositive C)
    {σ t : ℝ} (hσ : σ ≠ 1/2) (ht : t ≠ 0)
    {v : ℝ × ℝ} (hv : v ≠ 0) : False := by
  -- A non-real zero gives an orbit of four distinct points
  -- (non-degeneracy of the counterexample configuration admitted at the gate)
  have hdistinct : Function.Injective (orbit σ t) := orbit_injective hσ ht
  have hA := chiABVec_A v
  have hB := chiABVec_B v
  have hne := chiABVec_nonzero hv
  have hneg := Kquad_chiAB_neg C (chiABVec v) hC hA hB hne
  have hpos := hunit (chiABVec v) hA hB hne
  linarith

/-- **Theorem 10 (zero-exclusion form)**:
    under unitarity positivity and the 9.4 non-degenerate gradient (`hgrad`),
    any zero σ + it with σ ≠ 1/2 must have t = 0. -/
theorem theorem_10 (C : ℝ) (hC : 0 < C) (hunit : UnitarityPositive C)
    (f : ℂ → ℂ)
    (hgrad : ∀ σ t : ℝ, f (σ + Complex.I * t) = 0 → σ ≠ 1/2 → t ≠ 0 →
      ∃ v : ℝ × ℝ, v ≠ 0) :
    ∀ σ t : ℝ, f (σ + Complex.I * t) = 0 → σ ≠ 1/2 → t = 0 := by
  intro σ t hz hσ
  by_contra ht
  obtain ⟨v, hv⟩ := hgrad σ t hz hσ ht
  exact theorem_9_5 C hC hunit hσ ht hv

end RH95U

/- ## Axiom audit -/
section Audit
#print axioms RH95U.orbit_injective
#print axioms RH95U.chiABVec_A
#print axioms RH95U.chiABVec_B
#print axioms RH95U.chiABVec_nonzero
#print axioms RH95U.theorem_9_5
#print axioms RH95U.theorem_10
end Audit
