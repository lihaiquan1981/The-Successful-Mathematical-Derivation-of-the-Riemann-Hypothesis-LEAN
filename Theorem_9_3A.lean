/-
Li Haiquan
Jilin University of Chemical Technology, China
ORCID: https://orcid.org/0009-0000-7365-6535
Email: lihaiquan@jluct.edu.cn
-/

import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

open Complex Nat

noncomputable section

/-!
# Theorem 9.3A — Lean 4 / mathlib Formalization

Any double-reflection entire function f (entireness + f(s)=f(1-s) + Schwarz
reflection) admits a unique representation f(s) = g((s-1/2)²), where g is a
real-coefficient entire function.
-/

namespace RH93

variable {f : ℂ → ℂ}

/-- Translate to the center 1/2: h(z) = f(1/2+z) -/
def h (f : ℂ → ℂ) : ℂ → ℂ := fun z => f (1/2 + z)

lemma h_diff (hf : Differentiable ℂ f) : Differentiable ℂ (h f) :=
  hf.comp (by fun_prop)

/-- The functional equation s↦1-s is precisely the evenness of h -/
lemma h_even (h_sym : ∀ s, f s = f (1 - s)) : Function.Even (h f) := fun z => by
  show f (1/2 + -z) = f (1/2 + z)
  rw [h_sym]
  congr 1
  ring

/-- Schwarz reflection is inherited: h(conj z) = conj(h z) -/
lemma h_conj_inv (h_conj : ∀ s, f (star s) = star (f s)) :
    ∀ z, h f (star z) = star (h f z) := by
  intro z
  have hz : star (1/2 + z) = 1/2 + star z := by simp
  show f (1/2 + star z) = star (f (1/2 + z))
  rw [← hz]
  exact h_conj _

/-- Odd-order derivatives of an even function vanish at 0: odd powers die out -/
lemma odd_iteratedDeriv_zero (he : Function.Even (h f))
    {n : ℕ} (hn : Odd n) : iteratedDeriv n (h f) 0 = 0 := by
  have hcomp : iteratedDeriv n (fun z => h f (-z)) 0
      = (-1 : ℂ) ^ n * iteratedDeriv n (h f) (-0) := by
    rw [iteratedDeriv_comp_neg n (h f) 0]
    simp [smul_eq_mul]
  have hcongr : (fun z => h f (-z)) = h f := funext fun z => he z
  rw [hcongr] at hcomp
  simp only [neg_zero, hn.neg_one_pow] at hcomp
  have hc := hcomp
  set x := iteratedDeriv n (h f) 0 with hx
  have h1 : x = -x := by simpa using hc
  have h2 : 2 * x = 0 := by grind
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

/-- Taylor coefficients -/
def coeff (f : ℂ → ℂ) (n : ℕ) : ℂ := (n ! : ℂ)⁻¹ * iteratedDeriv n (h f) 0

/-- Taylor expansion of the entire function h at 0 (convergent on the whole
plane) -/
lemma h_taylor (hf : Differentiable ℂ f) (z : ℂ) :
    HasSum (fun n => coeff f n * z ^ n) (h f z) := by
  have ht := hasSum_taylorSeries_of_entire (h_diff hf) 0 z
  simp only [sub_zero] at ht
  refine ht.congr fun n => ?_
  simp [coeff, smul_eq_mul, mul_comm, mul_left_comm]

lemma h_summable (hf : Differentiable ℂ f) (z : ℂ) :
    Summable (fun n => coeff f n * z ^ n) :=
  (h_taylor hf z).summable

/-- Odd-order coefficients die out -/
lemma coeff_odd_zero (h_sym : ∀ s, f s = f (1 - s)) {n : ℕ} (hn : Odd n) :
    coeff f n = 0 := by
  simp [coeff, odd_iteratedDeriv_zero (h_even h_sym) hn]

/-- g: the entire-function candidate keeping only even coefficients -/
def g (f : ℂ → ℂ) (w : ℂ) : ℂ := ∑' k, coeff f (2 * k) * w ^ k

/-- The even subseries converges everywhere -/
lemma g_summable (hf : Differentiable ℂ f) (w : ℂ) :
    Summable (fun k => coeff f (2 * k) * w ^ k) := by
  have hz : (Complex.sqrt w) ^ 2 = w := by
    rw [Complex.sqrt, ← cpow_nat_mul]
    simp
  have hs := (h_summable hf (Complex.sqrt w)).comp_injective
    (show Function.Injective (fun k : ℕ => 2 * k) from fun a b hab => by
      dsimp only at hab; omega)
  have heq : (fun n => coeff f n * Complex.sqrt w ^ n) ∘ (fun k : ℕ => 2 * k)
      = fun k => coeff f (2 * k) * w ^ k := by
    funext k
    simp only [Function.comp_apply]
    rw [pow_mul, hz]
  rw [heq] at hs
  exact hs

/-- Main identity: h(z) = g(z²), the translated form of f(s) = g((s-1/2)²) -/
lemma h_eq_g_sq (hf : Differentiable ℂ f) (h_sym : ∀ s, f s = f (1 - s)) (z : ℂ) :
    h f z = g f (z ^ 2) := by
  set t : ℕ → ℂ := fun n => coeff f n * z ^ n with ht
  -- Even part: HasSum to g(z²)
  have heven : HasSum (fun k => t (2 * k)) (g f (z ^ 2)) := by
    have hs : Summable fun k => t (2 * k) := by
      have := g_summable hf (z ^ 2)
      refine this.congr fun k => ?_
      simp [ht, pow_mul]
    have hge : (∑' k, t (2 * k)) = g f (z ^ 2) := by
      rw [g]
      exact tsum_congr fun k => by simp [ht, pow_mul]
    rw [← hge]
    exact hs.hasSum
  -- Odd part: pointwise zero, HasSum to 0
  have hodd0 : ∀ k : ℕ, t (2 * k + 1) = 0 := by
    intro k
    have hc := coeff_odd_zero h_sym (n := 2 * k + 1) ⟨k, rfl⟩
    simp [ht, hc]
  have hodd : HasSum (fun k => t (2 * k + 1)) 0 := by
    have he : (fun k => t (2 * k + 1)) = fun _ => (0 : ℂ) := funext hodd0
    rw [he]
    exact hasSum_zero
  -- Even + odd = everything
  have hfull := HasSum.even_add_odd heven hodd
  rw [add_zero] at hfull
  exact (h_taylor hf z).unique hfull

/-- The power-series object of g (mathlib FMS wrapper) -/
def gFMS (f : ℂ → ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun k => coeff f (2 * k))

/-- g converges absolutely everywhere ⇒ radius of convergence ⊤ -/
lemma gFMS_radius (hf : Differentiable ℂ f) : (gFMS f).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  have hs := g_summable hf (((r : ℝ) : ℂ))
  have hs' : Summable fun k => ‖coeff f (2 * k) * (((r : ℝ) : ℂ)) ^ k‖ :=
    summable_norm_iff.mpr hs
  have hnorm : Summable fun k => ‖coeff f (2 * k)‖ * (r : ℝ) ^ k := by
    refine hs'.congr fun k => ?_
    simp [norm_pow]
  refine hnorm.congr fun k => ?_
  congr 1
  have hn : ‖(gFMS f) k‖ = ‖coeff f (2 * k)‖ := by
    delta gFMS
    rw [FormalMultilinearSeries.ofScalars_norm]
  rw [hn]

/-- g is entire -/
lemma g_diff (hf : Differentiable ℂ f) : Differentiable ℂ (g f) := by
  have hr : (gFMS f).radius = ⊤ := gFMS_radius hf
  have hp := (gFMS f).hasFPowerSeriesOnBall (by simp [hr])
  rw [hr] at hp
  have hd : DifferentiableOn ℂ (gFMS f).sum (Metric.eball 0 ⊤) := hp.differentiableOn
  rw [Metric.eball_top] at hd
  have hdiff : Differentiable ℂ (gFMS f).sum := differentiableOn_univ.mp hd
  have heq : (gFMS f).sum = g f := by
    funext w
    show FormalMultilinearSeries.ofScalarsSum (fun k => coeff f (2 * k)) w = g f w
    rw [FormalMultilinearSeries.ofScalarsSum_eq_tsum, g]
    exact tsum_congr fun k => by simp [smul_eq_mul]
  rw [heq] at hdiff
  exact hdiff

/-- Real-valued on the real axis ⇒ derivative real-valued (induction step of
the real-coefficient lemma) -/
lemma deriv_im_zero_of_im_zero {ψ : ℂ → ℂ} (hψ : Differentiable ℂ ψ)
    (hreal : ∀ t : ℝ, (ψ ↑t).im = 0) (t : ℝ) : (deriv ψ ↑t).im = 0 := by
  have hd : HasDerivAt ψ (deriv ψ ↑t) ↑t := (hψ ↑t).hasDerivAt
  have hd' : HasDerivAt (fun y : ℝ => ψ ↑y) (deriv ψ ↑t) t := hd.comp_ofReal
  have hval : ∀ y : ℝ, ψ ↑y = (((ψ ↑y).re : ℝ) : ℂ) := by
    intro y
    rw [Complex.ext_iff]
    exact ⟨by simp, by simp [hreal y]⟩
  have h3 : HasDerivAt (fun y : ℝ => (((ψ ↑y).re : ℝ) : ℂ)) (deriv ψ ↑t) t := by
    have he : (fun y : ℝ => (((ψ ↑y).re : ℝ) : ℂ)) = (fun y : ℝ => ψ ↑y) :=
      funext fun y => (hval y).symm
    rw [he]
    exact hd'
  have hdrv : DifferentiableAt ℝ (fun y : ℝ => (ψ ↑y).re) t := by
    have hca : DifferentiableAt ℝ (fun y : ℝ => ψ ↑y) t := hd'.differentiableAt
    exact Complex.reCLM.differentiableAt.comp t hca
  have h4 : HasDerivAt (fun y : ℝ => (((ψ ↑y).re : ℝ) : ℂ))
      ↑(deriv (fun y : ℝ => (ψ ↑y).re) t) t :=
    hdrv.hasDerivAt.ofReal_comp
  have h5 : deriv ψ ↑t = ↑(deriv (fun y : ℝ => (ψ ↑y).re) t) := h3.unique h4
  rw [h5]
  simp

/-- Derivatives of all orders are real-valued on the real axis (induction) -/
lemma iteratedDeriv_im_zero (hd : Differentiable ℂ (h f))
    (hc : ∀ z, h f (star z) = star (h f z)) :
    ∀ n : ℕ, ∀ t : ℝ, (iteratedDeriv n (h f) ↑t).im = 0 := by
  have hdn : ∀ n : ℕ, Differentiable ℂ (iteratedDeriv n (h f)) := by
    intro n
    induction n with
    | zero => simpa [iteratedDeriv_zero] using hd
    | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv
  intro n
  induction n with
  | zero =>
    intro t
    rw [iteratedDeriv_zero]
    have h1 : h f (star ↑t) = star (h f ↑t) := hc ↑t
    have h2 : star (↑t : ℂ) = ↑t := by simp
    rw [h2] at h1
    have h3 : star (h f ↑t) = h f ↑t := h1.symm
    exact (conj_eq_iff_im.mp h3)
  | succ n ih =>
    intro t
    rw [iteratedDeriv_succ]
    exact deriv_im_zero_of_im_zero (hdn n) ih t

/-- All coefficients of g are real -/
lemma g_real_coeff (hf : Differentiable ℂ f)
    (hc : ∀ z, h f (star z) = star (h f z)) (k : ℕ) :
    (coeff f (2 * k)).im = 0 := by
  have hd : Differentiable ℂ (h f) := h_diff hf
  have him := iteratedDeriv_im_zero hd hc (2 * k) 0
  rw [show ((0 : ℝ) : ℂ) = 0 by simp] at him
  rw [coeff]
  rw [Complex.mul_im]
  rw [him]
  simp [Complex.inv_im]


/-- g is real-valued on the real axis -/
lemma g_real_on_real (hf : Differentiable ℂ f)
    (h_conj : ∀ s, f (star s) = star (f s)) (t : ℝ) : (g f ↑t).im = 0 := by
  have hc := h_conj_inv (f := f) h_conj
  have hs : Summable fun k => coeff f (2 * k) * (↑t : ℂ) ^ k := g_summable hf ↑t
  have hmap : Complex.imCLM (g f ↑t) = ∑' k, Complex.imCLM (coeff f (2 * k) * (↑t : ℂ) ^ k) := by
    rw [g]
    exact Complex.imCLM.map_tsum hs
  have hterm : ∀ k : ℕ, Complex.imCLM (coeff f (2 * k) * (↑t : ℂ) ^ k) = 0 := by
    intro k
    rw [Complex.imCLM_apply, Complex.mul_im]
    have h1 : (coeff f (2 * k)).im = 0 := g_real_coeff hf hc k
    have h2 : ((↑t : ℂ) ^ k).im = 0 := by
      norm_cast
    simp [h1, h2]
  rw [← Complex.imCLM_apply, hmap]
  simp_rw [hterm]
  exact tsum_zero

/-- Representation form: f(s) = g((s−1/2)²) -/
lemma rep_form (hf : Differentiable ℂ f) (h_sym : ∀ s, f s = f (1 - s)) (s : ℂ) :
    f s = g f ((s - 1/2)^2) := by
  have hz : h f (s - 1/2) = g f ((s - 1/2)^2) := h_eq_g_sq hf h_sym (s - 1/2)
  have h1 : h f (s - 1/2) = f s := by
    show f (1/2 + (s - 1/2)) = f s
    congr 1
    ring
  rw [← h1]
  exact hz

/-- Uniqueness: the representing function is uniquely determined by f
(no analyticity hypothesis needed) -/
theorem unique_rep {g1 g2 : ℂ → ℂ}
    (h1 : ∀ s : ℂ, f s = g1 ((s - 1/2)^2))
    (h2 : ∀ s : ℂ, f s = g2 ((s - 1/2)^2)) : g1 = g2 := by
  funext w
  have hsq : (Complex.sqrt w)^2 = w := by
    rw [Complex.sqrt, ← cpow_nat_mul]
    simp
  have h1w := h1 (1/2 + Complex.sqrt w)
  have h2w := h2 (1/2 + Complex.sqrt w)
  have harg : (1/2 + Complex.sqrt w - 1/2)^2 = w := by
    have : (1/2 + Complex.sqrt w - 1/2 : ℂ) = Complex.sqrt w := by ring
    rw [this, hsq]
  rw [harg] at h1w h2w
  rw [h1w] at h2w
  exact h2w

/-- **Theorem 9.3A**: every double-reflection entire function has a unique
    representation f(s) = g((s−1/2)²), where g is a real-coefficient
    (real-valued on the real axis) entire function -/
theorem theorem_9_3A (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f s = f (1 - s))
    (h_conj : ∀ s, f (star s) = star (f s)) :
    (∃ g : ℂ → ℂ, Differentiable ℂ g ∧ (∀ t : ℝ, (g ↑t).im = 0) ∧
      (∀ s : ℂ, f s = g ((s - 1/2)^2))) ∧
    (∀ g1 g2 : ℂ → ℂ, (∀ s : ℂ, f s = g1 ((s - 1/2)^2)) →
      (∀ s : ℂ, f s = g2 ((s - 1/2)^2)) → g1 = g2) := by
  refine ⟨⟨g f, g_diff hf, g_real_on_real hf h_conj, rep_form hf h_sym⟩, ?_⟩
  intro g1 g2 h1 h2
  exact unique_rep h1 h2

end RH93

section Audit
#print axioms RH93.theorem_9_3A
#print axioms RH93.h_eq_g_sq
#print axioms RH93.g_diff
#print axioms RH93.g_real_coeff
#print axioms RH93.unique_rep
end Audit
