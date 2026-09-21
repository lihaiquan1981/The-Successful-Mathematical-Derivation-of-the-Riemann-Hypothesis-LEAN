import Mathlib
import Theorem_9_3A
import Lemma_9_4
import Lemma_11_3
import Lemma_9_5C

/-!
# Solution

Proves the six compared theorems of the structural group by the standalone
machine-verified developments of the repository:

* `structural_reduction_9_3A`     — `RH93.theorem_9_3A` (Theorem_9_3A.lean)
* `germ_structure_9_4`            — `RH94.lemma_9_4` (Lemma_9_4.lean)
* `real_axis_positivity_11_3`     — `RH113.lemma_11_3` (Lemma_11_3.lean)
* `xi_ne_zero_of_quotient_nonneg` — `RH113.xiFn_ne_zero_of_w_nonneg`
* `critical_line_lock`            — `RH113.critical_line_lock`
* `RHHeat.heat_kernel_spectral`   — `RH95C.lemma_9_5C` (Lemma_9_5C.lean),
  via the definitionally-equal field-data bridge `RHHeat.toRH95C`

Challenge and Solution are separate Lake libraries (Palomar template
layout); each compared declaration is restated here with the same
signature, in Mathlib-native terms, and closed by reduction to the
corresponding repository theorem.
-/

namespace RHStructural

/-- **Theorem 9.3A** (factorization of doubly reflected entire functions
    through the symmetry quotient). -/
theorem structural_reduction_9_3A {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f s = f (1 - s))
    (h_conj : ∀ s, f (star s) = star (f s)) :
    (∃ g : ℂ → ℂ, Differentiable ℂ g ∧ (∀ t : ℝ, (g ↑t).im = 0) ∧
      (∀ s : ℂ, f s = g ((s - 1/2)^2))) ∧
    (∀ g1 g2 : ℂ → ℂ, (∀ s : ℂ, f s = g1 ((s - 1/2)^2)) →
      (∀ s : ℂ, f s = g2 ((s - 1/2)^2)) → g1 = g2) :=
  RH93.theorem_9_3A hf h_sym h_conj

/-- **Lemma 9.4** (reflection structure of the local germ space). Proved by
    `RH94.lemma_9_4`; the repository's coordinate abbreviations
    (`RH94.vim`, `RH94.nablaV`, `RH95U.reflA`, `RH95U.reflB`) unfold to the
    Mathlib-native statements compared here. -/
theorem germ_structure_9_4 {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f s = f (1 - s))
    (h_conj : ∀ s, f (star s) = star (f s)) :
    (∀ u : ℝ × ℝ, (f (↑(1 - u.1) + ↑u.2 * Complex.I)).im =
      -(f (↑u.1 + ↑u.2 * Complex.I)).im)
    ∧ (∀ u : ℝ × ℝ, (f (↑u.1 + ↑(-u.2) * Complex.I)).im =
      -(f (↑u.1 + ↑u.2 * Complex.I)).im)
    ∧ (∀ y : ℝ, (f (↑(1 / 2 : ℝ) + ↑y * Complex.I)).im = 0)
    ∧ (∀ x : ℝ, (f (x : ℂ)).im = 0)
    ∧ (∀ σ γ : ℝ, deriv f (↑σ + ↑γ * Complex.I) ≠ 0 →
        (deriv (fun x : ℝ => (f (↑x + ↑γ * Complex.I)).im) σ,
          deriv (fun y : ℝ => (f (↑σ + ↑y * Complex.I)).im) γ) ≠ 0) := by
  obtain ⟨hA, hB, hLA, hLB, hgrad⟩ :=
    RH94.lemma_9_4 hf (fun s => (h_sym s).symm) h_conj
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u
    simpa [RH94.vim, RH95U.reflA] using hA u
  · intro u
    simpa [RH94.vim, RH95U.reflB] using hB u
  · intro y
    simpa [RH94.vim] using hLA y
  · intro x
    simpa [RH94.vim] using hLB x
  · intro σ γ hder
    simpa [RH94.nablaV, RH94.vim] using hgrad σ γ hder

/-- **Lemma 11.3** (real-axis positivity of Riemann's xi). Proved by
    `RH113.lemma_11_3`; `RH113.xiFn` unfolds to the factored form compared
    here. -/
theorem real_axis_positivity_11_3
    (hζ : ∀ x : ℝ, 0 < x → x < 1 → (riemannZeta (x : ℂ)).re < 0)
    {x : ℝ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    (0 : ℝ) < (((x : ℂ) * ((x : ℂ) - 1) / 2) * completedRiemannZeta (x : ℂ)).re ∧
    (((x : ℂ) * ((x : ℂ) - 1) / 2) * completedRiemannZeta (x : ℂ)).im = 0 := by
  have h := RH113.lemma_11_3 hζ hx0 hx1
  unfold RH113.xiFn at h
  exact h

/-- **Zero exclusion for nonnegative quotient coordinate**. Proved by
    `RH113.xiFn_ne_zero_of_w_nonneg`. -/
theorem xi_ne_zero_of_quotient_nonneg
    (hζ : ∀ x : ℝ, 0 < x → x < 1 → (riemannZeta (x : ℂ)).re < 0)
    {s : ℂ} {w : ℝ}
    (hw : (s - 1 / 2) ^ 2 = (w : ℂ)) (hw0 : 0 ≤ w) (hwq : w ≠ 1 / 4) :
    (s * (s - 1) / 2) * completedRiemannZeta s ≠ 0 := by
  have h := RH113.xiFn_ne_zero_of_w_nonneg hζ hw hw0 hwq
  unfold RH113.xiFn at h
  exact h

/-- **Critical-line lock**. Proved by `RH113.critical_line_lock`. -/
theorem critical_line_lock {s : ℂ} {w : ℝ}
    (hw : (s - 1 / 2) ^ 2 = (w : ℂ)) (hwneg : w < 0) :
    s.re = 1 / 2 :=
  RH113.critical_line_lock hw hwneg

end RHStructural

namespace RHHeat

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section

/-- Dot product of 2D vectors. -/
def dot (w u : ℝ × ℝ) : ℝ := w.1 * u.1 + w.2 * u.2

/-- Jacobian of reflection A: diag(−1,1). -/
def JA (u : ℝ × ℝ) : ℝ × ℝ := (-u.1, u.2)

/-- Jacobian of reflection B: diag(1,−1). -/
def JB (u : ℝ × ℝ) : ℝ × ℝ := (u.1, -u.2)

/-- A-reflection indices of the four-point orbit: 0↔1, 2↔3. -/
def iA : Fin 4 → Fin 4 := ![1, 0, 3, 2]

/-- B-reflection indices of the four-point orbit: 0↔2, 1↔3. -/
def iB : Fin 4 → Fin 4 := ![2, 3, 0, 1]

/-- 2D Euclidean norm. -/
def nrm2 (u : ℝ × ℝ) : ℝ := Real.sqrt (u.1 ^ 2 + u.2 ^ 2)

/-- Single-coordinate Gaussian measure N(0, α/2). -/
def G (α : ℝ) : Measure ℝ := gaussianReal 0 (Real.toNNReal (α / 2))

/-- 2D heat-kernel probability measure (product of two coordinates). -/
def P (α : ℝ) : Measure (ℝ × ℝ) := (G α).prod (G α)

instance (α : ℝ) : IsProbabilityMeasure (G α) :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal _ _))

instance (α : ℝ) : IsProbabilityMeasure (P α) :=
  inferInstanceAs (IsProbabilityMeasure ((G α).prod (G α)))

/-- Field data bundle: the field Φ, the four-point orbit s, the orbit
    gradients w, and the quadratic Taylor-remainder constant M. -/
structure FieldData where
  Φ : ℝ × ℝ → ℝ
  s : Fin 4 → ℝ × ℝ
  w : Fin 4 → ℝ × ℝ
  M : ℝ
  hM : 0 ≤ M
  hmeas : Measurable Φ
  hbound : ∃ B, 0 ≤ B ∧ ∀ z, |Φ z| ≤ B
  htaylor : ∀ i : Fin 4, ∀ u : ℝ × ℝ, |Φ (s i + u) - dot (w i) u| ≤ M * (nrm2 u) ^ 2

/-- Heat-kernel regularized geometric energy on the four-point orbit. -/
noncomputable def Egeom (D : FieldData) (C : ℝ) (α : ℝ) : ℝ :=
  (C/2) * ∑ i : Fin 4,
    ((∫ u : ℝ × ℝ, D.Φ (D.s i + u) * D.Φ (D.s (iA i) + JA u) ∂(P α))
    + ∫ u : ℝ × ℝ, D.Φ (D.s i + u) * D.Φ (D.s (iB i) + JB u) ∂(P α))

/-- The K̃ geometric quadratic form on the eight-dimensional gradient space. -/
noncomputable def Kquad (C : ℝ) (w : Fin 4 → ℝ × ℝ) : ℝ :=
  (C/4) * ∑ i : Fin 4, (dot (w i) (JA (w (iA i))) + dot (w i) (JB (w (iB i))))

/-- Bridge to the library field-data structure (definitionally equal fields). -/
def toRH95C (D : FieldData) : RH95C.FieldData where
  Φ := D.Φ
  s := D.s
  w := D.w
  M := D.M
  hM := D.hM
  hmeas := D.hmeas
  hbound := D.hbound
  htaylor := D.htaylor

/-- **Lemma 9.5C** (heat-kernel spectral limit for the two-channel orbit
    energy). (i) The rescaled regularized energy converges to the K̃
    quadratic form; (ii) on chi_AB-type configurations the limit form is
    strictly negative definite, ⟨W, K̃ W⟩ = −(C/2)‖W‖² < 0. -/
theorem heat_kernel_spectral (D : FieldData) (hC : 0 < C) :
    (Filter.Tendsto (fun α => Egeom D C α / α) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Kquad C D.w))) ∧
    ((∀ i, D.w (iA i) = JB (D.w i)) → (∀ i, D.w (iB i) = JA (D.w i)) →
      (∃ i : Fin 4, D.w i ≠ 0) → Kquad C D.w < 0) :=
  RH95C.lemma_9_5C (toRH95C D) hC

end

end RHHeat
