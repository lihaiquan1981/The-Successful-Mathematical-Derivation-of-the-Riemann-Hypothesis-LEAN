/-
Li Haiquan
Jilin University of Chemical Technology, China
ORCID: https://orcid.org/0009-0000-7365-6535
Email: lihaiquan@jluct.edu.cn
-/

import Unitarity_Assembly

/-!
# Lemma 9.4 (The χAB Structure of the Local Germ Space) — Lean 4 / mathlib Formalization

Corresponding to paragraphs 467–536 of the paper. Let f : ℂ → ℂ satisfy the
double-reflection symmetry:
  (A) f(1−s) = f(s)  (reflection symmetry about the critical line)
  (B) f(s̄) = conj(f(s))  (reflection symmetry about the real axis / conjugation)
Write v = Im(f) (a real-valued function, in real coordinates
vv (x,y) = Im(f(x+iy))).

Formalized content:
  (a) v is of χAB type: v(ιA s) = −v(s), v(ιB s) = −v(s)
      where ιA(x,y) = (1−x, y), ιB(x,y) = (x, −y)
  (b) v vanishes identically on L_A (the critical line Re = 1/2) and on L_B
      (the real axis)
  (c) simple zero (f'(ρ) ≠ 0) ⇒ ∇v(ρ) ≠ 0
      (Cauchy–Riemann: ∇v = (Im f′, Re f′), established rigorously via the
      ℝ-restriction chain rule for the complex derivative)
  and the four-point orbit gradient vector: the values of ∇v on the four-point
      orbit are exactly
      w = (a, b, a, −b, −a, b, −a, −b) = chiABVec(∇v(ρ)) (paragraph 522)
  Finally, an internal proof of the hgrad interface is given:
      simple zero ⇒ existence of a nonzero gradient vector.
-/

open RH95C RH95U

namespace RH94

/-- v = Im f in real coordinates -/
def vim (f : ℂ → ℂ) (u : ℝ × ℝ) : ℝ := (f (↑u.1 + ↑u.2 * Complex.I)).im



/-- (a) A channel: v(ιA u) = −v(u), where ιA(x,y) = (1−x, y) -/
lemma vim_reflA {f : ℂ → ℂ} (h_sym : ∀ s, f (1 - s) = f s)
    (h_conj : ∀ s, f (star s) = star (f s)) (u : ℝ × ℝ) :
    vim f (reflA u) = -vim f u := by
  have e : (↑(1 - u.1) + ↑u.2 * Complex.I : ℂ) = 1 - star (↑u.1 + ↑u.2 * Complex.I) := by
    simp [Complex.ext_iff]
  show (f (↑(1 - u.1) + ↑u.2 * Complex.I)).im = -(f (↑u.1 + ↑u.2 * Complex.I)).im
  rw [e, h_sym, h_conj, Complex.star_def, Complex.conj_im]

/-- (a) B channel: v(ιB u) = −v(u), where ιB(x,y) = (x, −y) -/
lemma vim_reflB {f : ℂ → ℂ} (h_conj : ∀ s, f (star s) = star (f s)) (u : ℝ × ℝ) :
    vim f (reflB u) = -vim f u := by
  have e : (↑u.1 + ↑(-u.2) * Complex.I : ℂ) = star (↑u.1 + ↑u.2 * Complex.I) := by
    simp
  show (f (↑u.1 + ↑(-u.2) * Complex.I)).im = -(f (↑u.1 + ↑u.2 * Complex.I)).im
  rw [e, h_conj, Complex.star_def, Complex.conj_im]

/-- (b) v ≡ 0 on the critical line (the fixed line Re = 1/2 of ιA) -/
lemma vim_critical_line {f : ℂ → ℂ} (h_sym : ∀ s, f (1 - s) = f s)
    (h_conj : ∀ s, f (star s) = star (f s)) (y : ℝ) : vim f (1/2, y) = 0 := by
  have h := vim_reflA h_sym h_conj (1/2, y)
  have hfix : reflA (1/2, y) = ((1/2, y) : ℝ × ℝ) := by
    show (1 - (1/2 : ℝ), y) = (1/2, y)
    norm_num
  rw [hfix] at h
  linarith [h]

/-- (b) v ≡ 0 on the real axis (the fixed line Im = 0 of ιB) -/
lemma vim_real_axis {f : ℂ → ℂ} (h_conj : ∀ s, f (star s) = star (f s)) (x : ℝ) :
    vim f (x, 0) = 0 := by
  have h := vim_reflB h_conj (x, 0)
  have hfix : reflB (x, 0) = ((x, 0) : ℝ × ℝ) := by simp [reflB]
  rw [hfix] at h
  linarith [h]

/-- Cauchy–Riemann core of (c) (x direction): ∂v/∂x = (f′).im.
    Chain rule: x ↦ x+iy (ℝ→ℂ, derivative ofRealCLM) composed with f
    (ℂ-differentiable, scalars restricted to ℝ), then take the imaginary part
    (imCLM). -/
lemma hasDerivAt_vim_x (hf : Differentiable ℂ f) (y x : ℝ) :
    HasDerivAt (fun x : ℝ => vim f (x, y)) (deriv f (↑x + ↑y * Complex.I)).im x := by
  have hg : HasFDerivAt (fun x : ℝ => (↑x + ↑y * Complex.I : ℂ)) Complex.ofRealCLM x :=
    (hasFDerivAt_add_const_iff _).mpr Complex.ofRealCLM.hasFDerivAt
  have hfF : HasFDerivAt f
      (ContinuousLinearMap.toSpanSingleton ℂ (deriv f (↑x + ↑y * Complex.I)))
      (↑x + ↑y * Complex.I) :=
    (hf _).hasDerivAt.hasFDerivAt
  have hcomp := (hfF.restrictScalars ℝ).comp x hg
  have him := Complex.imCLM.hasFDerivAt.comp x hcomp
  have hder := him.hasDerivAt
  have hval : (Complex.imCLM ∘L
        ((ContinuousLinearMap.toSpanSingleton ℂ (deriv f (↑x + ↑y * Complex.I))).restrictScalars ℝ
          ∘L Complex.ofRealCLM)) 1
      = (deriv f (↑x + ↑y * Complex.I)).im := by
    simp [ContinuousLinearMap.comp_apply, Complex.imCLM_apply, Complex.ofRealCLM_apply,
      ContinuousLinearMap.toSpanSingleton_apply]
  rw [hval] at hder
  exact hder

/-- Cauchy–Riemann core of (c) (y direction): ∂v/∂y = (f′).re -/
lemma hasDerivAt_vim_y (hf : Differentiable ℂ f) (x y : ℝ) :
    HasDerivAt (fun y : ℝ => vim f (x, y)) (deriv f (↑x + ↑y * Complex.I)).re y := by
  have hgfun : (fun y : ℝ => (↑x + ↑y * Complex.I : ℂ))
      = fun y : ℝ => (↑y * Complex.I + ↑x : ℂ) :=
    funext fun y => add_comm _ _
  have hg : HasFDerivAt (fun y : ℝ => (↑y * Complex.I + ↑x : ℂ))
      (Complex.ofRealCLM.smulRight Complex.I) y :=
    (hasFDerivAt_add_const_iff _).mpr (Complex.ofRealCLM.smulRight Complex.I).hasFDerivAt
  have hg' : HasFDerivAt (fun y : ℝ => (↑x + ↑y * Complex.I : ℂ))
      (Complex.ofRealCLM.smulRight Complex.I) y := hgfun ▸ hg
  have hfF : HasFDerivAt f
      (ContinuousLinearMap.toSpanSingleton ℂ (deriv f (↑x + ↑y * Complex.I)))
      (↑x + ↑y * Complex.I) :=
    (hf _).hasDerivAt.hasFDerivAt
  have hcomp := (hfF.restrictScalars ℝ).comp y hg'
  have him := Complex.imCLM.hasFDerivAt.comp y hcomp
  have hder := him.hasDerivAt
  have hval : (Complex.imCLM ∘L
        ((ContinuousLinearMap.toSpanSingleton ℂ (deriv f (↑x + ↑y * Complex.I))).restrictScalars ℝ
          ∘L (Complex.ofRealCLM.smulRight Complex.I))) 1
      = (deriv f (↑x + ↑y * Complex.I)).re := by
    simp [ContinuousLinearMap.comp_apply, Complex.imCLM_apply, Complex.ofRealCLM_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.toSpanSingleton_apply]
  rw [hval] at hder
  exact hder

/-- ∇v: the two real partial derivatives of v -/
noncomputable def nablaV (f : ℂ → ℂ) (u : ℝ × ℝ) : ℝ × ℝ :=
  (deriv (fun x => vim f (x, u.2)) u.1, deriv (fun y => vim f (u.1, y)) u.2)

lemma nablaV_fst (hf : Differentiable ℂ f) (u : ℝ × ℝ) :
    (nablaV f u).1 = (deriv f (↑u.1 + ↑u.2 * Complex.I)).im :=
  (hasDerivAt_vim_x hf u.2 u.1).deriv

lemma nablaV_snd (hf : Differentiable ℂ f) (u : ℝ × ℝ) :
    (nablaV f u).2 = (deriv f (↑u.1 + ↑u.2 * Complex.I)).re :=
  (hasDerivAt_vim_y hf u.1 u.2).deriv

/-- (c) Non-degenerate gradient at a simple zero: f′(ρ) ≠ 0 ⇒ ∇v(ρ) ≠ 0 -/
lemma nablaV_ne_zero (hf : Differentiable ℂ f) {u : ℝ × ℝ}
    (h : deriv f (↑u.1 + ↑u.2 * Complex.I) ≠ 0) : nablaV f u ≠ 0 := by
  intro hz
  apply h
  have h1 : (nablaV f u).1 = 0 := by rw [hz]; rfl
  have h2 : (nablaV f u).2 = 0 := by rw [hz]; rfl
  rw [nablaV_fst hf u] at h1
  rw [nablaV_snd hf u] at h2
  exact Complex.ext h2 h1

/-- A-reflection law of the gradient (paragraphs 504–510): ∇v(ιA u) = J_B (∇v u),
    i.e. (a, b) ↦ (a, −b) -/
lemma nablaV_reflA {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f (1 - s) = f s) (h_conj : ∀ s, f (star s) = star (f s))
    (u : ℝ × ℝ) : nablaV f (reflA u) = JB (nablaV f u) := by
  have hk : ∀ x : ℝ, HasDerivAt (fun x => vim f (x, u.2))
      ((deriv f (↑x + ↑u.2 * Complex.I)).im) x := fun x => hasDerivAt_vim_x hf u.2 x
  have hfst : deriv (fun x => vim f (x, u.2)) (1 - u.1)
      = deriv (fun x => vim f (x, u.2)) u.1 := by
    have hid : ∀ x : ℝ, vim f (x, u.2) = -vim f (1 - x, u.2) := fun x => by
      have h := vim_reflA h_sym h_conj (x, u.2)
      rw [show vim f (1 - x, u.2) = -vim f (x, u.2) from h]; simp
    have hmain : HasDerivAt (fun x => vim f (x, u.2))
        ((deriv f (↑u.1 + ↑u.2 * Complex.I)).im) (1 - u.1) := by
      have hinner : HasDerivAt (fun x : ℝ => 1 - x) (-1) (1 - u.1) :=
        (hasDerivAt_id' _).const_sub 1
      have hcomp := (hk (1 - (1 - u.1))).comp (1 - u.1) hinner
      have hneg := hcomp.neg
      have hval : -((deriv f (↑(1 - (1 - u.1)) + ↑u.2 * Complex.I)).im * -1)
          = (deriv f (↑u.1 + ↑u.2 * Complex.I)).im := by
        rw [sub_sub_self]; ring
      rw [hval] at hneg
      exact hneg.congr_of_eventuallyEq (Filter.Eventually.of_forall hid)
    rw [hmain.deriv, (hk u.1).deriv]
  have hsnd : deriv (fun y => vim f (1 - u.1, y)) u.2
      = -deriv (fun y => vim f (u.1, y)) u.2 := by
    have hid2 : (fun y => vim f (1 - u.1, y)) = fun y => -vim f (u.1, y) :=
      funext fun y => vim_reflA h_sym h_conj (u.1, y)
    rw [hid2]
    show deriv (-(fun y => vim f (u.1, y))) u.2 = _
    rw [(hasDerivAt_vim_y hf u.1 u.2).deriv]
    exact ((hasDerivAt_vim_y hf u.1 u.2).neg).deriv
  ext
  · exact hfst
  · exact hsnd

/-- B-reflection law of the gradient (paragraphs 511–517): ∇v(ιB u) = J_A (∇v u),
    i.e. (a, b) ↦ (−a, b) -/
lemma nablaV_reflB {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h_conj : ∀ s, f (star s) = star (f s))
    (u : ℝ × ℝ) : nablaV f (reflB u) = JA (nablaV f u) := by
  have hky : ∀ y : ℝ, HasDerivAt (fun y => vim f (u.1, y))
      ((deriv f (↑u.1 + ↑y * Complex.I)).re) y := fun y => hasDerivAt_vim_y hf u.1 y
  have hfst : deriv (fun x => vim f (x, -u.2)) u.1
      = -deriv (fun x => vim f (x, u.2)) u.1 := by
    have hid : (fun x => vim f (x, -u.2)) = fun x => -vim f (x, u.2) :=
      funext fun x => vim_reflB h_conj (x, u.2)
    rw [hid]
    show deriv (-(fun x => vim f (x, u.2))) u.1 = _
    rw [(hasDerivAt_vim_x hf u.2 u.1).deriv]
    exact ((hasDerivAt_vim_x hf u.2 u.1).neg).deriv
  have hsnd : deriv (fun y => vim f (u.1, y)) (-u.2)
      = deriv (fun y => vim f (u.1, y)) u.2 := by
    have hid : ∀ y : ℝ, vim f (u.1, y) = -vim f (u.1, -y) := fun y => by
      have h := vim_reflB h_conj (u.1, y)
      rw [show vim f (u.1, -y) = -vim f (u.1, y) from h]; simp
    have hmain : HasDerivAt (fun y => vim f (u.1, y))
        ((deriv f (↑u.1 + ↑u.2 * Complex.I)).re) (-u.2) := by
      have hinner : HasDerivAt (fun y : ℝ => -y) (-1) (-u.2) :=
        (hasDerivAt_id' _).neg
      have hcomp := (hky (- -u.2)).comp (-u.2) hinner
      have hneg := hcomp.neg
      have hval : -((deriv f (↑u.1 + ↑(- -u.2) * Complex.I)).re * -1)
          = (deriv f (↑u.1 + ↑u.2 * Complex.I)).re := by
        rw [show (- -u.2 : ℝ) = u.2 from neg_neg _]; ring
      rw [hval] at hneg
      exact hneg.congr_of_eventuallyEq (Filter.Eventually.of_forall hid)
    rw [hmain.deriv, (hky u.2).deriv]
  ext
  · exact hfst
  · exact hsnd

/-- The gradient field on the four-point orbit -/
noncomputable def orbitGrad (f : ℂ → ℂ) (σ γ : ℝ) : Fin 4 → ℝ × ℝ :=
  fun i => nablaV f (orbit σ γ i)

/-- The orbit gradient is exactly a χAB-type vector
    (paragraphs 518–522: w = (a, b, a, −b, −a, b, −a, −b)) -/
lemma orbitGrad_eq {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f (1 - s) = f s) (h_conj : ∀ s, f (star s) = star (f s))
    (σ γ : ℝ) : orbitGrad f σ γ = chiABVec (nablaV f (σ, γ)) := by
  funext i
  fin_cases i
  · rfl
  · exact nablaV_reflA hf h_sym h_conj (σ, γ)
  · exact nablaV_reflB hf h_conj (σ, γ)
  · show nablaV f (orbit σ γ 3) = chiABVec (nablaV f (σ, γ)) 3
    rw [show orbit σ γ 3 = reflA (reflB (σ, γ)) from rfl,
      nablaV_reflA hf h_sym h_conj (reflB (σ, γ)), nablaV_reflB hf h_conj (σ, γ)]
    rfl

/-- **Lemma 9.4** (the χAB structure of the local germ space):
    (a) v = Im f is of χAB type; (b) v vanishes on the critical line and the
    real axis; (c) f′(ρ) ≠ 0 ⇒ ∇v(ρ) ≠ 0. -/
theorem lemma_9_4 {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f (1 - s) = f s) (h_conj : ∀ s, f (star s) = star (f s)) :
    (∀ u : ℝ × ℝ, vim f (reflA u) = -vim f u)
    ∧ (∀ u : ℝ × ℝ, vim f (reflB u) = -vim f u)
    ∧ (∀ y : ℝ, vim f (1/2, y) = 0)
    ∧ (∀ x : ℝ, vim f (x, 0) = 0)
    ∧ (∀ σ γ : ℝ, deriv f (↑σ + ↑γ * Complex.I) ≠ 0 → nablaV f (σ, γ) ≠ 0) :=
  ⟨vim_reflA h_sym h_conj, vim_reflB h_conj,
   vim_critical_line h_sym h_conj, vim_real_axis h_conj,
   fun _ _ h => nablaV_ne_zero hf h⟩

/-- Internal implementation of the hgrad interface (a direct corollary of
    Lemma 9.4(c)): the simple-zero hypothesis (nonzero derivative at zeros)
    ⇒ existence of a nonzero gradient vector.
    Zero coordinates match the unitarity assembly file: ρ = σ + I·t. -/
theorem hgrad_of_simple_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hsimple : ∀ σ t : ℝ, f (↑σ + Complex.I * ↑t) = 0 →
      deriv f (↑σ + Complex.I * ↑t) ≠ 0) :
    ∀ σ t : ℝ, f (↑σ + Complex.I * ↑t) = 0 → σ ≠ 1/2 → t ≠ 0 →
      ∃ v : ℝ × ℝ, v ≠ 0 := by
  intro σ t hz _ _
  refine ⟨nablaV f (σ, t), nablaV_ne_zero hf ?_⟩
  show deriv f (↑σ + ↑t * Complex.I) ≠ 0
  have e : (↑σ + ↑t * Complex.I : ℂ) = ↑σ + Complex.I * ↑t := by rw [mul_comm]
  rw [e]
  exact hsimple σ t hz

end RH94


/- ## Axiom audit -/
section Audit
#print axioms RH94.vim_reflA
#print axioms RH94.vim_reflB
#print axioms RH94.vim_critical_line
#print axioms RH94.vim_real_axis
#print axioms RH94.hasDerivAt_vim_x
#print axioms RH94.hasDerivAt_vim_y
#print axioms RH94.nablaV_ne_zero
#print axioms RH94.nablaV_reflA
#print axioms RH94.nablaV_reflB
#print axioms RH94.orbitGrad_eq
#print axioms RH94.lemma_9_4
#print axioms RH94.hgrad_of_simple_zero
end Audit
