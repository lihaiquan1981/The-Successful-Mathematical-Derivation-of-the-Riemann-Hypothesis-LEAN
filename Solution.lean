import Mathlib
import Theorem_9_3A
import Lemma_9_4
import Lemma_11_3
import Lemma_9_5C
import MotherEquation_CoreVerification

/-!
# Solution

Proves the eight compared theorems of the structural and spectral group by
the standalone machine-verified developments of the repository:

* `structural_reduction_9_3A`        — `RH93.theorem_9_3A` (Theorem_9_3A.lean)
* `germ_structure_9_4`               — `RH94.lemma_9_4` (Lemma_9_4.lean)
* `real_axis_positivity_11_3`        — `RH113.lemma_11_3` (Lemma_11_3.lean)
* `xi_ne_zero_of_quotient_nonneg`    — `RH113.xiFn_ne_zero_of_w_nonneg`
* `critical_line_lock`               — `RH113.critical_line_lock`
* `RHHeat.heat_kernel_spectral`      — `RH95C.lemma_9_5C` (limit and
  negativity) together with `RH95C.Kquad_chiAB` (the explicit limit-form
  identity), via the definitionally-equal field-data bridge
  `RHHeat.toRH95C` (Lemma_9_5C.lean)
* `RHMother.two_channel_kernel_spectrum` — `MotherEquation.rK_eig_chi0/chiA/
  chiB/chiAB`, `MotherEquation.unitarity_sign`, `MotherEquation.phase_cliff`
  (MotherEquation_CoreVerification.lean)
* `RHMother.jet_lift_inheritance`    — `MotherEquation.jet_eigenvalue`,
  `MotherEquation.jet_energy`, `MotherEquation.jet_negative`

Challenge and Solution are separate Lake libraries (Palomar template
layout); each compared declaration is restated here with the same
signature and closed by reduction to the corresponding repository theorem.
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

/-- Field data bundle: the field Φ, the four centers s, the center
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

/-- **Lemma 9.5C** (heat-kernel spectral limit with the explicit limit
    form). Limit and negativity: `RH95C.lemma_9_5C`; the identity
    ⟨W, K̃ W⟩ = −(C/2)·Σᵢ‖wᵢ‖²: `RH95C.Kquad_chiAB`. The repository's
    abbreviations (`RH95C.Kquad`, `RH95C.nrm2`, `RH95C.iA/iB`,
    `RH95C.JA/JB`) are definitionally equal to the copies above. -/
theorem heat_kernel_spectral (D : FieldData) (hC : 0 < C) :
    (Filter.Tendsto (fun α => Egeom D C α / α) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Kquad C D.w))) ∧
    ((∀ i, D.w (iA i) = JB (D.w i)) → (∀ i, D.w (iB i) = JA (D.w i)) →
      Kquad C D.w = -(C/2) * ∑ i : Fin 4, (nrm2 (D.w i)) ^ 2) ∧
    ((∀ i, D.w (iA i) = JB (D.w i)) → (∀ i, D.w (iB i) = JA (D.w i)) →
      (∃ i : Fin 4, D.w i ≠ 0) → Kquad C D.w < 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (RH95C.lemma_9_5C (toRH95C D) hC).1
  · intro hA hB
    exact RH95C.Kquad_chiAB C D.w hA hB
  · exact (RH95C.lemma_9_5C (toRH95C D) hC).2

end

end RHHeat

namespace RHMother

/-- Integer 4-vectors: fields on the four-point orbit (doubled normalization). -/
abbrev V4v := Int × Int × Int × Int

/-- Scalar multiplication on orbit fields. -/
def smul4 (s : Int) (v : V4v) : V4v := (s * v.1, s * v.2.1, s * v.2.2.1, s * v.2.2.2)

/-- Addition on orbit fields. -/
def vadd4 (u v : V4v) : V4v := (u.1 + v.1, u.2.1 + v.2.1, u.2.2.1 + v.2.2.1, u.2.2.2 + v.2.2.2)

/-- The four eigenmodes: trivial / χA / χB / χAB. -/
def v0 : V4v := (1, 1, 1, 1)
def vA : V4v := (1, -1, 1, -1)
def vB : V4v := (1, 1, -1, -1)
def vAB : V4v := (1, -1, -1, 1)

/-- Doubled-normalization geometric kernel G = C·(KA+KB). -/
def gK (C : Int) (v : V4v) : V4v :=
  (C * (v.2.1 + v.2.2.1), C * (v.1 + v.2.2.2), C * (v.1 + v.2.2.2), C * (v.2.1 + v.2.2.1))

/-- Doubled-normalization regularized kernel R = G + 2εI. -/
def rK (C ε : Int) (v : V4v) : V4v := vadd4 (gK C v) (smul4 (2 * ε) v)

/-- Minimal-eigenvalue function: −2C+2ε on the expanded orbit, 2ε on the
    collapsed orbit. -/
def minEig (collapsed : Bool) (C ε : Int) : Int :=
  if collapsed then 2 * ε else -2 * C + 2 * ε

/-- **Two-channel kernel spectrum**. Proved by the Mother-Equation core
    certificate (`MotherEquation.rK_eig_*`, `MotherEquation.unitarity_sign`,
    `MotherEquation.phase_cliff`); the repository's definitions are
    definitionally equal to the copies above. -/
theorem two_channel_kernel_spectrum (C ε : Int) (hC : C > ε) (hε : ε > 0) :
    (rK C ε v0 = smul4 (2 * C + 2 * ε) v0)
    ∧ (rK C ε vA = smul4 (2 * ε) vA)
    ∧ (rK C ε vB = smul4 (2 * ε) vB)
    ∧ (rK C ε vAB = smul4 (-2 * C + 2 * ε) vAB)
    ∧ (-2 * C + 2 * ε < 0 ∧ 2 * C + 2 * ε > 0 ∧ 2 * ε > 0)
    ∧ (minEig false C ε < 0 ∧ minEig true C ε > 0 ∧
        minEig true C ε - minEig false C ε = 2 * C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact MotherEquation.rK_eig_chi0 C ε
  · exact MotherEquation.rK_eig_chiA C ε
  · exact MotherEquation.rK_eig_chiB C ε
  · exact MotherEquation.rK_eig_chiAB C ε
  · exact MotherEquation.unitarity_sign C ε hC hε
  · exact MotherEquation.phase_cliff C ε hC hε

/-- Integer 8-vectors: gradient jets on the four-point orbit. -/
abbrev V8 := Int × Int × Int × Int × Int × Int × Int × Int

/-- Gradient pattern of a simple zero (the χAB-type vector forced by the
    double-reflection symmetry). -/
def W8 (a b : Int) : V8 := (a, b, a, -b, -a, b, -a, -b)

/-- The 8-dimensional doubled-normalization geometric kernel. -/
def g8 (C : Int) (w : V8) : V8 :=
  match w with
  | (x1, y1, x2, y2, x3, y3, x4, y4) =>
    (C * (-x2 + x3), C * (y2 - y3),
     C * (-x1 + x4), C * (y1 - y4),
     C * (-x4 + x1), C * (y4 - y1),
     C * (-x3 + x2), C * (y3 - y2))

/-- Scalar multiplication on jet vectors. -/
def smul8 (s : Int) (w : V8) : V8 :=
  match w with
  | (x1, y1, x2, y2, x3, y3, x4, y4) =>
    (s * x1, s * y1, s * x2, s * y2, s * x3, s * y3, s * x4, s * y4)

/-- Addition on jet vectors. -/
def vadd8 (u v : V8) : V8 :=
  match u, v with
  | (x1, y1, x2, y2, x3, y3, x4, y4), (x1', y1', x2', y2', x3', y3', x4', y4') =>
    (x1 + x1', y1 + y1', x2 + x2', y2 + y2', x3 + x3', y3 + y3', x4 + x4', y4 + y4')

/-- The 8-dimensional regularized kernel R8 = G8 + 2εI. -/
def r8 (C ε : Int) (w : V8) : V8 := vadd8 (g8 C w) (smul8 (2 * ε) w)

/-- Dot product on jet vectors. -/
def dot8 (u v : V8) : Int :=
  match u, v with
  | (x1, y1, x2, y2, x3, y3, x4, y4), (x1', y1', x2', y2', x3', y3', x4', y4') =>
    x1 * x1' + y1 * y1' + x2 * x2' + y2 * y2' + x3 * x3' + y3 * y3' + x4 * x4' + y4 * y4'

/-- **Jet lift inheritance**. Proved by `MotherEquation.jet_eigenvalue`,
    `MotherEquation.jet_energy` and `MotherEquation.jet_negative`. -/
theorem jet_lift_inheritance (C ε a b : Int) (hC : C > ε) (hε : ε > 0) :
    (r8 C ε (W8 a b) = smul8 (-2 * C + 2 * ε) (W8 a b))
    ∧ (dot8 (W8 a b) (r8 C ε (W8 a b)) = 4 * (a * a + b * b) * (-2 * C + 2 * ε))
    ∧ ((a ≠ 0 ∨ b ≠ 0) → dot8 (W8 a b) (r8 C ε (W8 a b)) < 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact MotherEquation.jet_eigenvalue C ε a b
  · exact MotherEquation.jet_energy C ε a b
  · intro hne
    exact MotherEquation.jet_negative C ε a b hC hε hne

end RHMother
