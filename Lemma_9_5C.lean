/-
Li Haiquan
Jilin University of Chemical Technology, China
ORCID: https://orcid.org/0009-0000-7365-6535
Email: lihaiquan@jluct.edu.cn
-/

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic

/-!
# Lemma 9.5C (Heat-Kernel Regularization Limit) — Lean 4 / mathlib Formalization

Object: the heat-kernel regularized geometric energy on the four-point orbit
  E(α)[Φ] = (C/2) Σᵢ ∫ ρ_α(u) Φ(sᵢ+u) Φ(sᵢᴬ+J_A u) dλ + (B channel likewise)
where ρ_α is the 2D Gaussian probability measure with variance α/2
(i.e. the paper's δ(α)(z) = (πα)⁻¹e^{−‖z‖²/α}).

Formalized content:
1. Gaussian second moments: E[u_p²] = α/2, E[u₁u₂] = 0 (the "Gaussian second
   moment formula" of Step 3)
2. Main-term identity: ∫ ρ (w·u)(w'·Ju) = (α/2)(w·Jᵀw') (Step 3 main term)
3. Exact scaling laws of the third and fourth moments:
   m₃(α) = (√α)³·C₃, m₄(α) = α²·C₄ (Step 4 remainder scaling)
4. Pointwise limit: (1/α)E(α)[Φ] → ⟨W, K̃W⟩ (Claim (i))
5. χAB eigenvalue inheritance: on χAB-type W, ⟨W,K̃W⟩ = −(C/2)‖W‖² < 0 (Claim (ii))

Note: the Taylor remainder bound |Φ(sᵢ+u) − wᵢ·u| ≤ M‖u‖² in Claim (i) of the
paper is given as a hypothesis (the standard Taylor estimate for C² functions);
all other analysis is machine-proved. (See `Lemma_9_5C_TaylorRemainder.lean`,
where this hypothesis is discharged as the theorem `taylor_remainder_C2`.)
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section

namespace RH95C

/-- Dot product of 2D vectors -/
def dot (w u : ℝ × ℝ) : ℝ := w.1 * u.1 + w.2 * u.2

/-- Jacobian of reflection A: diag(−1,1) (self-adjoint, orthogonal) -/
def JA (u : ℝ × ℝ) : ℝ × ℝ := (-u.1, u.2)

/-- Jacobian of reflection B: diag(1,−1) (self-adjoint, orthogonal) -/
def JB (u : ℝ × ℝ) : ℝ × ℝ := (u.1, -u.2)

/-- Single-coordinate Gaussian measure N(0, α/2) -/
def G (α : ℝ) : Measure ℝ := gaussianReal 0 (Real.toNNReal (α / 2))

/-- 2D heat-kernel probability measure (probabilistic form of the paper's δ(α)) -/
def P (α : ℝ) : Measure (ℝ × ℝ) := (G α).prod (G α)

instance (α : ℝ) : IsProbabilityMeasure (G α) :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal _ _))

instance (α : ℝ) : IsProbabilityMeasure (P α) :=
  inferInstanceAs (IsProbabilityMeasure ((G α).prod (G α)))

section Moments

variable {α : ℝ}

/-- First moment vanishes -/
lemma integral_id_G : ∫ x : ℝ, x ∂(G α) = 0 :=
  integral_id_gaussianReal

/-- Second moment: ∫ x² dN(0,α/2) = α/2 (1D form of the Gaussian second moment formula) -/
lemma moment2 (hα : 0 < α) : ∫ x : ℝ, x ^ 2 ∂(G α) = α / 2 := by
  have h1 : Var[id; G α] = ↑(Real.toNNReal (α / 2)) := variance_id_gaussianReal
  rw [variance_eq_integral (by fun_prop)] at h1
  have h2 : (∫ x : ℝ, id x ∂(G α)) = 0 := integral_id_gaussianReal
  rw [h2] at h1
  simp only [sub_zero] at h1
  have h4 : (↑(Real.toNNReal (α / 2)) : ℝ) = α / 2 :=
    Real.coe_toNNReal _ (le_of_lt (half_pos hα))
  rw [h4] at h1
  exact h1

/-- x² is integrable -/
lemma integ_sq : Integrable (fun x : ℝ => x ^ 2) (G α) := by
  have h := (memLp_id_gaussianReal (μ := (0:ℝ)) (v := Real.toNNReal (α / 2))
    2).integrable_norm_rpow (by norm_num) (by norm_num)
  have heq : (fun x : ℝ => ‖id x‖ ^ (↑(2 : ℝ≥0) : ℝ≥0∞).toReal) = fun x => x ^ 2 := by
    funext x
    simp [id, sq_abs]
  rw [heq] at h
  exact h

/-- id is integrable -/
lemma integ_id : Integrable (fun x : ℝ => x) (G α) :=
  (memLp_id_gaussianReal (μ := (0:ℝ)) (v := Real.toNNReal (α / 2)) 1).integrable (by norm_num)

/-- Constant integral over a probability measure -/
lemma integral_one_G : ∫ _ : ℝ, (1 : ℝ) ∂(G α) = 1 := by
  rw [integral_const]
  simp

/-- The u₁² moment over the product measure = α/2 -/
lemma prod_moment_xx (hα : 0 < α) : ∫ u : ℝ × ℝ, u.1 ^ 2 ∂(P α) = α / 2 := by
  have h1 := integral_prod_mul (μ := G α) (ν := G α) (fun x : ℝ => x ^ 2) (fun _ : ℝ => (1 : ℝ))
  rw [moment2 hα, integral_one_G, mul_one] at h1
  simpa [P] using h1

/-- The u₂² moment over the product measure = α/2 -/
lemma prod_moment_yy (hα : 0 < α) : ∫ u : ℝ × ℝ, u.2 ^ 2 ∂(P α) = α / 2 := by
  have h1 := integral_prod_mul (μ := G α) (ν := G α) (fun _ : ℝ => (1 : ℝ)) (fun y : ℝ => y ^ 2)
  rw [moment2 hα, integral_one_G, one_mul] at h1
  simpa [P] using h1

/-- Cross moment vanishes: ∫ u₁u₂ = 0 (independence) -/
lemma prod_moment_xy : ∫ u : ℝ × ℝ, u.1 * u.2 ∂(P α) = 0 := by
  have h1 := integral_prod_mul (μ := G α) (ν := G α) (fun x : ℝ => x) (fun y : ℝ => y)
  rw [integral_id_G] at h1
  simpa [P] using h1

end Moments

section Scaling

variable {α : ℝ}

/-- 2D Euclidean norm -/
def nrm2 (u : ℝ × ℝ) : ℝ := Real.sqrt (u.1 ^ 2 + u.2 ^ 2)

lemma nrm2_nonneg (u : ℝ × ℝ) : 0 ≤ nrm2 u := Real.sqrt_nonneg _

lemma nrm2_continuous : Continuous nrm2 := by
  unfold nrm2
  continuity

lemma nrm2_measurable_pow (n : ℕ) : Measurable (fun u : ℝ × ℝ => (nrm2 u) ^ n) :=
  (nrm2_continuous.pow n).measurable

lemma nrm2_scale (c : ℝ) (hc : 0 ≤ c) (u : ℝ × ℝ) :
    nrm2 (c * u.1, c * u.2) = c * nrm2 u := by
  unfold nrm2
  rw [mul_pow, mul_pow, ← mul_add, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- Standard third-moment constant (E‖u‖³ at α = 1) -/
def C3 : ℝ := ∫ u : ℝ × ℝ, (nrm2 u) ^ 3 ∂(P 1)

/-- Standard fourth-moment constant (E‖u‖⁴ at α = 1) -/
def C4 : ℝ := ∫ u : ℝ × ℝ, (nrm2 u) ^ 4 ∂(P 1)

/-- Scaling law of the single-coordinate Gaussian: stretching by √α sends N(0,1/2) to N(0,α/2) -/
lemma map_G (hα : 0 < α) : (G 1).map (fun x => Real.sqrt α * x) = G α := by
  have h := gaussianReal_map_const_mul (μ := (0:ℝ)) (v := Real.toNNReal (1/2)) (Real.sqrt α)
  rw [mul_zero] at h
  have hv : NNReal.mk ((Real.sqrt α)^2) (sq_nonneg _) * Real.toNNReal (1/2 : ℝ)
      = Real.toNNReal (α/2) := by
    rw [← NNReal.coe_inj, NNReal.coe_mul]
    simp only [NNReal.coe_mk, Real.coe_toNNReal']
    rw [Real.sq_sqrt hα.le, max_eq_left (show (0:ℝ) ≤ 1/2 by norm_num),
      max_eq_left (le_of_lt (half_pos hα))]
    ring
  rw [hv] at h
  exact h

/-- Scaling law of the 2D heat-kernel measure -/
lemma map_P (hα : 0 < α) :
    (P 1).map (fun u : ℝ × ℝ => (Real.sqrt α * u.1, Real.sqrt α * u.2)) = P α := by
  have hm : Measurable (fun x : ℝ => Real.sqrt α * x) := Measurable.const_mul measurable_id _
  have h := Measure.map_prod_map (G 1) (G 1) hm hm
  rw [map_G hα] at h
  have hmap : Prod.map (fun x : ℝ => Real.sqrt α * x) (fun x : ℝ => Real.sqrt α * x)
      = fun u : ℝ × ℝ => (Real.sqrt α * u.1, Real.sqrt α * u.2) := rfl
  rw [hmap] at h
  exact h.symm

/-- Exact scaling law of the third moment: m₃(α) = (√α)³·C₃
    (the strict form of ~α^{3/2} in Step 4) -/
lemma m3_scaling (hα : 0 < α) :
    ∫ u : ℝ × ℝ, (nrm2 u) ^ 3 ∂(P α) = (Real.sqrt α) ^ 3 * C3 := by
  rw [← map_P hα]
  rw [integral_map (by fun_prop : Measurable
    (fun u : ℝ × ℝ => (Real.sqrt α * u.1, Real.sqrt α * u.2))).aemeasurable
    (nrm2_measurable_pow 3).aestronglyMeasurable]
  have hpw : ∀ u : ℝ × ℝ, (nrm2 (Real.sqrt α * u.1, Real.sqrt α * u.2)) ^ 3
      = (Real.sqrt α) ^ 3 * (nrm2 u) ^ 3 := by
    intro u
    rw [nrm2_scale (Real.sqrt α) (Real.sqrt_nonneg α) u, mul_pow]
  simp_rw [hpw]
  rw [integral_const_mul]
  rfl

/-- Exact scaling law of the fourth moment: m₄(α) = α²·C₄
    (the strict form of ~α² in Step 4) -/
lemma m4_scaling (hα : 0 < α) :
    ∫ u : ℝ × ℝ, (nrm2 u) ^ 4 ∂(P α) = α ^ 2 * C4 := by
  rw [← map_P hα]
  rw [integral_map (by fun_prop : Measurable
    (fun u : ℝ × ℝ => (Real.sqrt α * u.1, Real.sqrt α * u.2))).aemeasurable
    (nrm2_measurable_pow 4).aestronglyMeasurable]
  have hs4 : (Real.sqrt α) ^ 4 = α ^ 2 := by
    have h1 : (Real.sqrt α) ^ 2 = α := Real.sq_sqrt hα.le
    calc (Real.sqrt α) ^ 4 = ((Real.sqrt α) ^ 2) ^ 2 := by ring
      _ = α ^ 2 := by rw [h1]
  have hpw : ∀ u : ℝ × ℝ, (nrm2 (Real.sqrt α * u.1, Real.sqrt α * u.2)) ^ 4
      = α ^ 2 * (nrm2 u) ^ 4 := by
    intro u
    rw [nrm2_scale (Real.sqrt α) (Real.sqrt_nonneg α) u, mul_pow, hs4]
  simp_rw [hpw]
  rw [integral_const_mul]
  rfl

/-- |x|³ is integrable w.r.t. N(0,1/2) -/
lemma integ_abs3_G1 : Integrable (fun x : ℝ => |x| ^ 3) (G 1) := by
  have h := (memLp_id_gaussianReal (μ := (0:ℝ)) (v := Real.toNNReal (1/2))
    3).integrable_norm_rpow (by norm_num) (by norm_num)
  have heq : (fun x : ℝ => ‖id x‖ ^ (↑(3 : ℝ≥0) : ℝ≥0∞).toReal) = fun x => |x| ^ 3 := by
    funext x
    simp [id]
  rw [heq] at h
  exact h

/-- |x|⁴ is integrable w.r.t. N(0,1/2) -/
lemma integ_abs4_G1 : Integrable (fun x : ℝ => |x| ^ 4) (G 1) := by
  have h := (memLp_id_gaussianReal (μ := (0:ℝ)) (v := Real.toNNReal (1/2))
    4).integrable_norm_rpow (by norm_num) (by norm_num)
  have heq : (fun x : ℝ => ‖id x‖ ^ (↑(4 : ℝ≥0) : ℝ≥0∞).toReal) = fun x => |x| ^ 4 := by
    funext x
    simp [id]
  rw [heq] at h
  exact h

/-- Third moment is finite: C₃ is the integral of an integrable function
    (well-definedness of the Step 4 remainder) -/
lemma integ_nrm3_P1 : Integrable (fun u : ℝ × ℝ => (nrm2 u) ^ 3) (P 1) := by
  have h1 : Integrable (fun u : ℝ × ℝ => |u.1| ^ 3) (P 1) := integ_abs3_G1.comp_fst (G 1)
  have h2 : Integrable (fun u : ℝ × ℝ => |u.2| ^ 3) (P 1) := integ_abs3_G1.comp_snd (G 1)
  refine ((h1.add h2).const_mul 4).mono' (nrm2_measurable_pow 3).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  have hnn : 0 ≤ nrm2 u := nrm2_nonneg u
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hle : nrm2 u ≤ |u.1| + |u.2| := by
    unfold nrm2
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [add_sq, sq_abs, sq_abs]
    have h0 : 0 ≤ 2 * |u.1| * |u.2| := by positivity
    linarith [h0]
  calc (nrm2 u) ^ 3 ≤ (|u.1| + |u.2|) ^ 3 := pow_le_pow_left₀ hnn hle 3
    _ ≤ 4 * (|u.1| ^ 3 + |u.2| ^ 3) := by
        have key : |u.1| ^ 2 * |u.2| + |u.1| * |u.2| ^ 2 ≤ |u.1| ^ 3 + |u.2| ^ 3 := by
          have h := mul_nonneg (sq_nonneg (|u.1| - |u.2|))
            (add_nonneg (abs_nonneg u.1) (abs_nonneg u.2))
          nlinarith [abs_nonneg u.1, abs_nonneg u.2]
        nlinarith [abs_nonneg u.1, abs_nonneg u.2]

/-- Fourth moment is finite: C₄ is the integral of an integrable function -/
lemma integ_nrm4_P1 : Integrable (fun u : ℝ × ℝ => (nrm2 u) ^ 4) (P 1) := by
  have h1 : Integrable (fun u : ℝ × ℝ => |u.1| ^ 4) (P 1) := integ_abs4_G1.comp_fst (G 1)
  have h2 : Integrable (fun u : ℝ × ℝ => |u.2| ^ 4) (P 1) := integ_abs4_G1.comp_snd (G 1)
  refine ((h1.add h2).const_mul 8).mono' (nrm2_measurable_pow 4).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  have hnn : 0 ≤ nrm2 u := nrm2_nonneg u
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hle : nrm2 u ≤ |u.1| + |u.2| := by
    unfold nrm2
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [add_sq, sq_abs, sq_abs]
    have h0 : 0 ≤ 2 * |u.1| * |u.2| := by positivity
    linarith [h0]
  calc (nrm2 u) ^ 4 ≤ (|u.1| + |u.2|) ^ 4 := pow_le_pow_left₀ hnn hle 4
    _ ≤ 8 * (|u.1| ^ 4 + |u.2| ^ 4) := by
        set a := |u.1| with ha
        set b := |u.2| with hb
        have h1' : a ^ 2 * b ^ 2 * 6 ≤ 3 * (a ^ 4 + b ^ 4) := by
          have h := sq_nonneg (a ^ 2 - b ^ 2)
          nlinarith [sq_nonneg (a ^ 2 - b ^ 2)]
        have h2' : 4 * (a ^ 3 * b + a * b ^ 3) ≤ 4 * (a ^ 4 + b ^ 4) := by
          have h := mul_nonneg (sq_nonneg (a - b))
            (show 0 ≤ a ^ 2 + a * b + b ^ 2 by positivity)
          nlinarith [h]
        nlinarith [abs_nonneg u.1, abs_nonneg u.2]

end Scaling

section MainTerm

variable {α : ℝ}

/-- Cauchy–Schwarz (2D): |w·u| ≤ ‖w‖·‖u‖ -/
lemma dot_bound (w u : ℝ × ℝ) : |dot w u| ≤ nrm2 w * nrm2 u := by
  have hsq : (dot w u) ^ 2 ≤ (nrm2 w) ^ 2 * (nrm2 u) ^ 2 := by
    unfold dot nrm2
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    nlinarith [sq_nonneg (w.1 * u.2 - w.2 * u.1)]
  have h1 : |dot w u| = Real.sqrt ((dot w u) ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
  rw [h1]
  calc Real.sqrt ((dot w u) ^ 2) ≤ Real.sqrt ((nrm2 w) ^ 2 * (nrm2 u) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt ((nrm2 w * nrm2 u) ^ 2) := by rw [mul_pow]
    _ = nrm2 w * nrm2 u := Real.sqrt_sq (mul_nonneg (nrm2_nonneg _) (nrm2_nonneg _))

/-- JA preserves the norm -/
lemma nrm2_JA (u : ℝ × ℝ) : nrm2 (JA u) = nrm2 u := by
  unfold nrm2 JA
  rw [neg_sq]

/-- JB preserves the norm -/
lemma nrm2_JB (u : ℝ × ℝ) : nrm2 (JB u) = nrm2 u := by
  unfold nrm2 JB
  rw [neg_sq]

/-- u₁² is integrable over P α -/
lemma integ_xx : Integrable (fun u : ℝ × ℝ => u.1 ^ 2) (P α) :=
  (integ_sq (α := α)).comp_fst (G α)

/-- u₂² is integrable over P α -/
lemma integ_yy : Integrable (fun u : ℝ × ℝ => u.2 ^ 2) (P α) :=
  (integ_sq (α := α)).comp_snd (G α)

/-- u₁u₂ is integrable over P α -/
lemma integ_xy : Integrable (fun u : ℝ × ℝ => u.1 * u.2) (P α) := by
  have h := (integ_id (α := α)).smul_prod (integ_id (α := α))
  simp only [smul_eq_mul] at h
  exact h

/-- Main-term identity (with sign parameters):
    ∫ ρ (w·u)(ε₁w'₁u₁+ε₂w'₂u₂) = (α/2)(ε₁w₁w'₁+ε₂w₂w'₂).
    Cross moments vanish, leaving only diagonal contributions — the Gaussian
    second moment formula of Step 3 of the paper. -/
lemma channel_main (hα : 0 < α) (w w' : ℝ × ℝ) (e1 e2 : ℝ) :
    ∫ u : ℝ × ℝ, dot w u * (e1 * w'.1 * u.1 + e2 * w'.2 * u.2) ∂(P α)
      = (α/2) * (e1 * (w.1 * w'.1) + e2 * (w.2 * w'.2)) := by
  have hexp : (fun u : ℝ × ℝ => dot w u * (e1 * w'.1 * u.1 + e2 * w'.2 * u.2))
      = fun u => (e1 * w'.1 * w.1) * u.1 ^ 2
        + (e2 * w'.2 * w.1 + e1 * w'.1 * w.2) * (u.1 * u.2)
        + (e2 * w'.2 * w.2) * u.2 ^ 2 := by
    funext u
    simp only [dot]
    ring
  rw [hexp]
  have i1 : Integrable (fun u : ℝ × ℝ => (e1 * w'.1 * w.1) * u.1 ^ 2) (P α) :=
    (integ_xx (α := α)).const_mul _
  have i2 : Integrable (fun u : ℝ × ℝ => (e2 * w'.2 * w.1 + e1 * w'.1 * w.2) * (u.1 * u.2)) (P α) :=
    (integ_xy (α := α)).const_mul _
  have i3 : Integrable (fun u : ℝ × ℝ => (e2 * w'.2 * w.2) * u.2 ^ 2) (P α) :=
    (integ_yy (α := α)).const_mul _
  have step1 : (∫ u : ℝ × ℝ, (e1 * w'.1 * w.1) * u.1 ^ 2
        + (e2 * w'.2 * w.1 + e1 * w'.1 * w.2) * (u.1 * u.2)
        + (e2 * w'.2 * w.2) * u.2 ^ 2 ∂(P α))
      = (∫ u : ℝ × ℝ, (e1 * w'.1 * w.1) * u.1 ^ 2
        + (e2 * w'.2 * w.1 + e1 * w'.1 * w.2) * (u.1 * u.2) ∂(P α))
        + ∫ u : ℝ × ℝ, (e2 * w'.2 * w.2) * u.2 ^ 2 ∂(P α) :=
    integral_add (i1.add i2) i3
  have step2 : (∫ u : ℝ × ℝ, (e1 * w'.1 * w.1) * u.1 ^ 2
        + (e2 * w'.2 * w.1 + e1 * w'.1 * w.2) * (u.1 * u.2) ∂(P α))
      = (∫ u : ℝ × ℝ, (e1 * w'.1 * w.1) * u.1 ^ 2 ∂(P α))
        + ∫ u : ℝ × ℝ, (e2 * w'.2 * w.1 + e1 * w'.1 * w.2) * (u.1 * u.2) ∂(P α) :=
    integral_add i1 i2
  rw [step1, step2]
  have e1' : (∫ u : ℝ × ℝ, (e1 * w'.1 * w.1) * u.1 ^ 2 ∂(P α))
      = (e1 * w'.1 * w.1) * (α / 2) := by
    rw [integral_const_mul]
    congr 1
    exact prod_moment_xx hα
  have e2' : (∫ u : ℝ × ℝ, (e2 * w'.2 * w.1 + e1 * w'.1 * w.2) * (u.1 * u.2) ∂(P α))
      = (e2 * w'.2 * w.1 + e1 * w'.1 * w.2) * 0 := by
    rw [integral_const_mul]
    congr 1
    exact prod_moment_xy
  have e3' : (∫ u : ℝ × ℝ, (e2 * w'.2 * w.2) * u.2 ^ 2 ∂(P α))
      = (e2 * w'.2 * w.2) * (α / 2) := by
    rw [integral_const_mul]
    congr 1
    exact prod_moment_yy hα
  rw [e1', e2', e3']
  ring

/-- A-channel main term: ∫ ρ (w·u)(w'·J_Au) = (α/2)(w·J_Aw') -/
lemma main_A (hα : 0 < α) (w w' : ℝ × ℝ) :
    ∫ u : ℝ × ℝ, dot w u * dot w' (JA u) ∂(P α) = (α/2) * dot w (JA w') := by
  have h := channel_main hα w w' (-1) 1
  have hfun : (fun u : ℝ × ℝ => dot w u * ((-1) * w'.1 * u.1 + 1 * w'.2 * u.2))
      = fun u => dot w u * dot w' (JA u) := by
    funext u
    simp only [dot, JA]
    ring
  rw [hfun] at h
  rw [h]
  simp only [dot, JA]
  ring

/-- B-channel main term: ∫ ρ (w·u)(w'·J_Bu) = (α/2)(w·J_Bw') -/
lemma main_B (hα : 0 < α) (w w' : ℝ × ℝ) :
    ∫ u : ℝ × ℝ, dot w u * dot w' (JB u) ∂(P α) = (α/2) * dot w (JB w') := by
  have h := channel_main hα w w' 1 (-1)
  have hfun : (fun u : ℝ × ℝ => dot w u * (1 * w'.1 * u.1 + (-1) * w'.2 * u.2))
      = fun u => dot w u * dot w' (JB u) := by
    funext u
    simp only [dot, JB]
    ring
  rw [hfun] at h
  rw [h]
  simp only [dot, JB]
  ring

end MainTerm

section Energy

/-- A-reflection indices of the four-point orbit: 0↔1, 2↔3 -/
def iA : Fin 4 → Fin 4 := ![1, 0, 3, 2]

/-- B-reflection indices of the four-point orbit: 0↔2, 1↔3 -/
def iB : Fin 4 → Fin 4 := ![2, 3, 0, 1]

/-- Field data bundle: Φ, the four-point orbit s, gradients w at the orbit points,
    and the Taylor remainder constant M (= ½‖Φ‖_{C²}).
    htaylor is the standard first-order Taylor remainder estimate for a C² smooth
    field at points where Φ(sᵢ)=0. -/
structure FieldData where
  Φ : ℝ × ℝ → ℝ
  s : Fin 4 → ℝ × ℝ
  w : Fin 4 → ℝ × ℝ
  M : ℝ
  hM : 0 ≤ M
  hmeas : Measurable Φ
  hbound : ∃ B, 0 ≤ B ∧ ∀ z, |Φ z| ≤ B
  htaylor : ∀ i : Fin 4, ∀ u : ℝ × ℝ, |Φ (s i + u) - dot (w i) u| ≤ M * (nrm2 u) ^ 2

/-- Heat-kernel regularized geometric energy (paragraph 593 of the paper; per the
    paper's parenthetical note, the integral is extended to the whole space) -/
def Egeom (D : FieldData) (C : ℝ) (α : ℝ) : ℝ :=
  (C/2) * ∑ i : Fin 4,
    ((∫ u : ℝ × ℝ, D.Φ (D.s i + u) * D.Φ (D.s (iA i) + JA u) ∂(P α))
    + ∫ u : ℝ × ℝ, D.Φ (D.s i + u) * D.Φ (D.s (iB i) + JB u) ∂(P α))

/-- The K̃ geometric quadratic form: ⟨W, K̃ W⟩ (main-term coefficient of Step 5) -/
def Kquad (C : ℝ) (w : Fin 4 → ℝ × ℝ) : ℝ :=
  (C/4) * ∑ i : Fin 4, (dot (w i) (JA (w (iA i))) + dot (w i) (JB (w (iB i))))

/-- Total gradient scale constant -/
def T1 (D : FieldData) : ℝ :=
  ∑ i : Fin 4, (nrm2 (D.w i) + nrm2 (D.w (iA i))) + ∑ i : Fin 4, (nrm2 (D.w i) + nrm2 (D.w (iB i)))

/-- nrm2³ is integrable under the heat-kernel measure for any α > 0 -/
lemma integ_nrm3 (hα : 0 < α) : Integrable (fun u : ℝ × ℝ => (nrm2 u) ^ 3) (P α) := by
  rw [← map_P hα]
  rw [integrable_map_measure (nrm2_measurable_pow 3).aestronglyMeasurable
    (by fun_prop : Measurable (fun u : ℝ × ℝ => (Real.sqrt α * u.1, Real.sqrt α * u.2))).aemeasurable]
  have heq : (fun u : ℝ × ℝ => (nrm2 u) ^ 3)
      ∘ (fun u : ℝ × ℝ => (Real.sqrt α * u.1, Real.sqrt α * u.2))
      = fun u => (Real.sqrt α) ^ 3 * (nrm2 u) ^ 3 := by
    funext u
    simp only [Function.comp_apply]
    rw [nrm2_scale (Real.sqrt α) (Real.sqrt_nonneg α) u, mul_pow]
  rw [heq]
  exact integ_nrm3_P1.const_mul _

/-- nrm2⁴ is integrable under the heat-kernel measure for any α > 0 -/
lemma integ_nrm4 (hα : 0 < α) : Integrable (fun u : ℝ × ℝ => (nrm2 u) ^ 4) (P α) := by
  rw [← map_P hα]
  rw [integrable_map_measure (nrm2_measurable_pow 4).aestronglyMeasurable
    (by fun_prop : Measurable (fun u : ℝ × ℝ => (Real.sqrt α * u.1, Real.sqrt α * u.2))).aemeasurable]
  have heq : (fun u : ℝ × ℝ => (nrm2 u) ^ 4)
      ∘ (fun u : ℝ × ℝ => (Real.sqrt α * u.1, Real.sqrt α * u.2))
      = fun u => α ^ 2 * (nrm2 u) ^ 4 := by
    funext u
    simp only [Function.comp_apply]
    rw [nrm2_scale (Real.sqrt α) (Real.sqrt_nonneg α) u, mul_pow,
      show (Real.sqrt α) ^ 4 = ((Real.sqrt α) ^ 2) ^ 2 by ring, Real.sq_sqrt hα.le]
  rw [heq]
  exact integ_nrm4_P1.const_mul _

/-- nrm2² is integrable -/
lemma integ_nrm2sq : Integrable (fun u : ℝ × ℝ => (nrm2 u) ^ 2) (P α) := by
  have heq : (fun u : ℝ × ℝ => (nrm2 u) ^ 2) = fun u => u.1 ^ 2 + u.2 ^ 2 := by
    funext u
    unfold nrm2
    rw [Real.sq_sqrt (by positivity)]
  rw [heq]
  exact (integ_xx (α := α)).add (integ_yy (α := α))

/-- Single-channel decomposition and remainder bound (core estimate of Steps 3–4) -/
lemma channel_bound (D : FieldData) (hα : 0 < α)
    (si sii : ℝ × ℝ) (wi wii : ℝ × ℝ) (J : ℝ × ℝ → ℝ × ℝ)
    (hnJ : ∀ u, nrm2 (J u) = nrm2 u) (hmJ : Measurable J)
    (ht_i : ∀ u, |D.Φ (si + u) - dot wi u| ≤ D.M * (nrm2 u) ^ 2)
    (ht_ii : ∀ u, |D.Φ (sii + u) - dot wii u| ≤ D.M * (nrm2 u) ^ 2)
    (V : ℝ)
    (hmain : ∫ u : ℝ × ℝ, dot wi u * dot wii (J u) ∂(P α) = (α/2) * V) :
    |∫ u : ℝ × ℝ, D.Φ (si + u) * D.Φ (sii + J u) ∂(P α) - (α/2) * V|
      ≤ (nrm2 wi + nrm2 wii) * D.M * (∫ u : ℝ × ℝ, (nrm2 u) ^ 3 ∂(P α))
        + D.M ^ 2 * (∫ u : ℝ × ℝ, (nrm2 u) ^ 4 ∂(P α)) := by
  obtain ⟨B, hB0, hB⟩ := D.hbound
  set a : ℝ × ℝ → ℝ := fun u => D.Φ (si + u) with ha
  set b : ℝ × ℝ → ℝ := fun u => dot wi u with hb
  set aJ : ℝ × ℝ → ℝ := fun u => D.Φ (sii + J u) with haJ
  set bJ : ℝ × ℝ → ℝ := fun u => dot wii (J u) with hbJ
  have hma : Measurable a := D.hmeas.comp (by fun_prop)
  have hmaJ : Measurable aJ := D.hmeas.comp ((measurable_const_add _).comp hmJ)
  have hmb : Measurable b := by
    show Measurable fun u : ℝ × ℝ => dot wi u
    unfold dot
    fun_prop
  have hmbJ : Measurable bJ := by
    show Measurable fun u : ℝ × ℝ => dot wii (J u)
    unfold dot
    fun_prop
  have hr : ∀ u, |a u - b u| ≤ D.M * (nrm2 u) ^ 2 := ht_i
  have hrJ : ∀ u, |aJ u - bJ u| ≤ D.M * (nrm2 u) ^ 2 := by
    intro u
    have h := ht_ii (J u)
    rw [hnJ u] at h
    exact h
  -- Integrability of each block
  have ibb : Integrable (fun u => b u * bJ u) (P α) := by
    refine ((integ_nrm2sq (α := α)).const_mul (nrm2 wi * nrm2 wii)).mono'
      (hmb.mul hmbJ).aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |b u| * |bJ u| ≤ (nrm2 wi * nrm2 u) * (nrm2 wii * nrm2 (J u)) :=
          mul_le_mul (dot_bound wi u) (dot_bound wii (J u)) (abs_nonneg _)
            (mul_nonneg (nrm2_nonneg _) (nrm2_nonneg _))
      _ = (nrm2 wi * nrm2 wii) * (nrm2 u) ^ 2 := by rw [hnJ u]; ring
  have ibr : Integrable (fun u => b u * (aJ u - bJ u)) (P α) := by
    refine ((integ_nrm3 hα).const_mul (nrm2 wi * D.M)).mono'
      (hmb.mul (hmaJ.sub hmbJ)).aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |b u| * |aJ u - bJ u| ≤ (nrm2 wi * nrm2 u) * (D.M * (nrm2 u) ^ 2) :=
          mul_le_mul (dot_bound wi u) (hrJ u) (abs_nonneg _)
            (mul_nonneg (nrm2_nonneg _) (nrm2_nonneg _))
      _ = (nrm2 wi * D.M) * (nrm2 u) ^ 3 := by ring
  have irb : Integrable (fun u => (a u - b u) * bJ u) (P α) := by
    refine ((integ_nrm3 hα).const_mul (D.M * nrm2 wii)).mono'
      ((hma.sub hmb).mul hmbJ).aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |a u - b u| * |bJ u| ≤ (D.M * (nrm2 u) ^ 2) * (nrm2 wii * nrm2 (J u)) :=
          mul_le_mul (hr u) (dot_bound wii (J u)) (abs_nonneg _)
            (mul_nonneg D.hM (by positivity))
      _ = (D.M * nrm2 wii) * (nrm2 u) ^ 3 := by rw [hnJ u]; ring
  have irr : Integrable (fun u => (a u - b u) * (aJ u - bJ u)) (P α) := by
    refine ((integ_nrm4 hα).const_mul (D.M ^ 2)).mono'
      ((hma.sub hmb).mul (hmaJ.sub hmbJ)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |a u - b u| * |aJ u - bJ u| ≤ (D.M * (nrm2 u) ^ 2) * (D.M * (nrm2 u) ^ 2) :=
          mul_le_mul (hr u) (hrJ u) (abs_nonneg _) (mul_nonneg D.hM (by positivity))
      _ = D.M ^ 2 * (nrm2 u) ^ 4 := by ring
  -- Algebraic decomposition
  have hdecomp : (fun u => a u * aJ u)
      = (fun u => b u * bJ u) + (fun u => b u * (aJ u - bJ u))
        + (fun u => (a u - b u) * bJ u) + (fun u => (a u - b u) * (aJ u - bJ u)) := by
    funext u
    simp only [Pi.add_apply]
    ring
  have hsplit : ∫ u : ℝ × ℝ, a u * aJ u ∂(P α)
      = ∫ u : ℝ × ℝ, b u * bJ u ∂(P α)
        + ∫ u : ℝ × ℝ, b u * (aJ u - bJ u) ∂(P α)
        + ∫ u : ℝ × ℝ, (a u - b u) * bJ u ∂(P α)
        + ∫ u : ℝ × ℝ, (a u - b u) * (aJ u - bJ u) ∂(P α) := by
    have s1 : (∫ u : ℝ × ℝ, a u * aJ u ∂(P α))
        = (∫ u : ℝ × ℝ, b u * bJ u + b u * (aJ u - bJ u) + (a u - b u) * bJ u ∂(P α))
          + ∫ u : ℝ × ℝ, (a u - b u) * (aJ u - bJ u) ∂(P α) := by
      rw [hdecomp]
      exact integral_add' ((ibb.add ibr).add irb) irr
    have s2 : (∫ u : ℝ × ℝ, b u * bJ u + b u * (aJ u - bJ u) + (a u - b u) * bJ u ∂(P α))
        = (∫ u : ℝ × ℝ, b u * bJ u + b u * (aJ u - bJ u) ∂(P α))
          + ∫ u : ℝ × ℝ, (a u - b u) * bJ u ∂(P α) :=
      integral_add' (ibb.add ibr) irb
    have s3 : (∫ u : ℝ × ℝ, b u * bJ u + b u * (aJ u - bJ u) ∂(P α))
        = (∫ u : ℝ × ℝ, b u * bJ u ∂(P α)) + ∫ u : ℝ × ℝ, b u * (aJ u - bJ u) ∂(P α) :=
      integral_add' ibb ibr
    rw [s1, s2, s3]
  -- Estimates of the three error terms
  have e1 : |∫ u : ℝ × ℝ, b u * (aJ u - bJ u) ∂(P α)|
      ≤ (nrm2 wi * D.M) * (∫ u : ℝ × ℝ, (nrm2 u) ^ 3 ∂(P α)) := by
    calc |∫ u : ℝ × ℝ, b u * (aJ u - bJ u) ∂(P α)|
        ≤ ∫ u : ℝ × ℝ, |b u * (aJ u - bJ u)| ∂(P α) := abs_integral_le_integral_abs
      _ ≤ ∫ u : ℝ × ℝ, (nrm2 wi * D.M) * (nrm2 u) ^ 3 ∂(P α) := by
          refine integral_mono_ae (ibr.norm) ((integ_nrm3 hα).const_mul _)
            (Filter.Eventually.of_forall fun u => ?_)
          show |b u * (aJ u - bJ u)| ≤ nrm2 wi * D.M * nrm2 u ^ 3
          rw [abs_mul]
          calc |b u| * |aJ u - bJ u| ≤ (nrm2 wi * nrm2 u) * (D.M * (nrm2 u) ^ 2) :=
                mul_le_mul (dot_bound wi u) (hrJ u) (abs_nonneg _)
                  (mul_nonneg (nrm2_nonneg _) (nrm2_nonneg _))
            _ = (nrm2 wi * D.M) * (nrm2 u) ^ 3 := by ring
      _ = (nrm2 wi * D.M) * (∫ u : ℝ × ℝ, (nrm2 u) ^ 3 ∂(P α)) := integral_const_mul _ _
  have e2 : |∫ u : ℝ × ℝ, (a u - b u) * bJ u ∂(P α)|
      ≤ (D.M * nrm2 wii) * (∫ u : ℝ × ℝ, (nrm2 u) ^ 3 ∂(P α)) := by
    calc |∫ u : ℝ × ℝ, (a u - b u) * bJ u ∂(P α)|
        ≤ ∫ u : ℝ × ℝ, |(a u - b u) * bJ u| ∂(P α) := abs_integral_le_integral_abs
      _ ≤ ∫ u : ℝ × ℝ, (D.M * nrm2 wii) * (nrm2 u) ^ 3 ∂(P α) := by
          refine integral_mono_ae (irb.norm) ((integ_nrm3 hα).const_mul _)
            (Filter.Eventually.of_forall fun u => ?_)
          show |(a u - b u) * bJ u| ≤ D.M * nrm2 wii * nrm2 u ^ 3
          rw [abs_mul]
          calc |a u - b u| * |bJ u| ≤ (D.M * (nrm2 u) ^ 2) * (nrm2 wii * nrm2 (J u)) :=
                mul_le_mul (hr u) (dot_bound wii (J u)) (abs_nonneg _)
                  (mul_nonneg D.hM (by positivity))
            _ = (D.M * nrm2 wii) * (nrm2 u) ^ 3 := by rw [hnJ u]; ring
      _ = (D.M * nrm2 wii) * (∫ u : ℝ × ℝ, (nrm2 u) ^ 3 ∂(P α)) := integral_const_mul _ _
  have e3 : |∫ u : ℝ × ℝ, (a u - b u) * (aJ u - bJ u) ∂(P α)|
      ≤ D.M ^ 2 * (∫ u : ℝ × ℝ, (nrm2 u) ^ 4 ∂(P α)) := by
    calc |∫ u : ℝ × ℝ, (a u - b u) * (aJ u - bJ u) ∂(P α)|
        ≤ ∫ u : ℝ × ℝ, |(a u - b u) * (aJ u - bJ u)| ∂(P α) := abs_integral_le_integral_abs
      _ ≤ ∫ u : ℝ × ℝ, D.M ^ 2 * (nrm2 u) ^ 4 ∂(P α) := by
          refine integral_mono_ae (irr.norm) ((integ_nrm4 hα).const_mul _)
            (Filter.Eventually.of_forall fun u => ?_)
          show |(a u - b u) * (aJ u - bJ u)| ≤ D.M ^ 2 * nrm2 u ^ 4
          rw [abs_mul]
          calc |a u - b u| * |aJ u - bJ u| ≤ (D.M * (nrm2 u) ^ 2) * (D.M * (nrm2 u) ^ 2) :=
                mul_le_mul (hr u) (hrJ u) (abs_nonneg _) (mul_nonneg D.hM (by positivity))
            _ = D.M ^ 2 * (nrm2 u) ^ 4 := by ring
      _ = D.M ^ 2 * (∫ u : ℝ × ℝ, (nrm2 u) ^ 4 ∂(P α)) := integral_const_mul _ _
  -- Combine
  have hsum : ∫ u : ℝ × ℝ, a u * aJ u ∂(P α) - (α/2) * V
      = ∫ u : ℝ × ℝ, b u * (aJ u - bJ u) ∂(P α)
        + ∫ u : ℝ × ℝ, (a u - b u) * bJ u ∂(P α)
        + ∫ u : ℝ × ℝ, (a u - b u) * (aJ u - bJ u) ∂(P α) := by
    rw [hsplit, hmain]
    ring
  rw [hsum]
  calc |∫ u : ℝ × ℝ, b u * (aJ u - bJ u) ∂(P α)
        + ∫ u : ℝ × ℝ, (a u - b u) * bJ u ∂(P α)
        + ∫ u : ℝ × ℝ, (a u - b u) * (aJ u - bJ u) ∂(P α)|
      ≤ |∫ u : ℝ × ℝ, b u * (aJ u - bJ u) ∂(P α)|
        + |∫ u : ℝ × ℝ, (a u - b u) * bJ u ∂(P α)|
        + |∫ u : ℝ × ℝ, (a u - b u) * (aJ u - bJ u) ∂(P α)| := by
        exact le_trans (abs_add_le _ _) (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (nrm2 wi * D.M) * (∫ u : ℝ × ℝ, (nrm2 u) ^ 3 ∂(P α))
        + (D.M * nrm2 wii) * (∫ u : ℝ × ℝ, (nrm2 u) ^ 3 ∂(P α))
        + D.M ^ 2 * (∫ u : ℝ × ℝ, (nrm2 u) ^ 4 ∂(P α)) := add_le_add (add_le_add e1 e2) e3
    _ = (nrm2 wi + nrm2 wii) * D.M * (∫ u : ℝ × ℝ, (nrm2 u) ^ 3 ∂(P α))
        + D.M ^ 2 * (∫ u : ℝ × ℝ, (nrm2 u) ^ 4 ∂(P α)) := by ring

/-- Main term + remainder ⇒ energy error bound (quantitative form of Claim (i)) -/
lemma energy_error_bound (D : FieldData) (hC : 0 ≤ C) (hα : 0 < α) :
    |Egeom D C α - α * Kquad C D.w|
      ≤ (C/2) * (D.M * T1 D * ((Real.sqrt α) ^ 3 * C3) + 8 * D.M ^ 2 * (α ^ 2 * C4)) := by
  have hnJA : ∀ u, nrm2 (JA u) = nrm2 u := nrm2_JA
  have hnJB : ∀ u, nrm2 (JB u) = nrm2 u := nrm2_JB
  have hmJA : Measurable JA := by unfold JA; fun_prop
  have hmJB : Measurable JB := by unfold JB; fun_prop
  set m3 := ∫ u : ℝ × ℝ, (nrm2 u) ^ 3 ∂(P α) with hm3
  set m4 := ∫ u : ℝ × ℝ, (nrm2 u) ^ 4 ∂(P α) with hm4
  -- Per-point, per-channel error
  have perA : ∀ i : Fin 4, |∫ u : ℝ × ℝ, D.Φ (D.s i + u) * D.Φ (D.s (iA i) + JA u) ∂(P α)
      - (α/2) * dot (D.w i) (JA (D.w (iA i)))|
      ≤ (nrm2 (D.w i) + nrm2 (D.w (iA i))) * D.M * m3 + D.M ^ 2 * m4 := fun i =>
    channel_bound D hα (D.s i) (D.s (iA i)) (D.w i) (D.w (iA i)) JA hnJA hmJA
      (D.htaylor i) (D.htaylor (iA i)) _ (main_A hα (D.w i) (D.w (iA i)))
  have perB : ∀ i : Fin 4, |∫ u : ℝ × ℝ, D.Φ (D.s i + u) * D.Φ (D.s (iB i) + JB u) ∂(P α)
      - (α/2) * dot (D.w i) (JB (D.w (iB i)))|
      ≤ (nrm2 (D.w i) + nrm2 (D.w (iB i))) * D.M * m3 + D.M ^ 2 * m4 := fun i =>
    channel_bound D hα (D.s i) (D.s (iB i)) (D.w i) (D.w (iB i)) JB hnJB hmJB
      (D.htaylor i) (D.htaylor (iB i)) _ (main_B hα (D.w i) (D.w (iB i)))
  -- Rewrite Egeom − α·Kquad as (C/2) times the sum of per-point errors
  have hrewrite : Egeom D C α - α * Kquad C D.w
      = (C/2) * ∑ i : Fin 4,
        ((∫ u : ℝ × ℝ, D.Φ (D.s i + u) * D.Φ (D.s (iA i) + JA u) ∂(P α)
          - (α/2) * dot (D.w i) (JA (D.w (iA i))))
        + (∫ u : ℝ × ℝ, D.Φ (D.s i + u) * D.Φ (D.s (iB i) + JB u) ∂(P α)
          - (α/2) * dot (D.w i) (JB (D.w (iB i))))) := by
    unfold Egeom Kquad
    rw [← mul_assoc, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hrewrite, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ C/2)]
  calc (C/2) * |∑ i : Fin 4,
        ((∫ u : ℝ × ℝ, D.Φ (D.s i + u) * D.Φ (D.s (iA i) + JA u) ∂(P α)
          - (α/2) * dot (D.w i) (JA (D.w (iA i))))
        + (∫ u : ℝ × ℝ, D.Φ (D.s i + u) * D.Φ (D.s (iB i) + JB u) ∂(P α)
          - (α/2) * dot (D.w i) (JB (D.w (iB i)))))|
      ≤ (C/2) * ∑ i : Fin 4,
        (|(∫ u : ℝ × ℝ, D.Φ (D.s i + u) * D.Φ (D.s (iA i) + JA u) ∂(P α)
          - (α/2) * dot (D.w i) (JA (D.w (iA i))))|
        + |(∫ u : ℝ × ℝ, D.Φ (D.s i + u) * D.Φ (D.s (iB i) + JB u) ∂(P α)
          - (α/2) * dot (D.w i) (JB (D.w (iB i))))|) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => abs_add_le _ _)
    _ ≤ (C/2) * ∑ i : Fin 4,
        (((nrm2 (D.w i) + nrm2 (D.w (iA i))) * D.M * m3 + D.M ^ 2 * m4)
        + ((nrm2 (D.w i) + nrm2 (D.w (iB i))) * D.M * m3 + D.M ^ 2 * m4)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact Finset.sum_le_sum fun i _ => add_le_add (perA i) (perB i)
    _ = (C/2) * (D.M * T1 D * m3 + 8 * D.M ^ 2 * m4) := by
        have hsumA : (∑ i : Fin 4, ((nrm2 (D.w i) + nrm2 (D.w (iA i))) * D.M * m3
                + D.M ^ 2 * m4))
            = D.M * m3 * (∑ i : Fin 4, (nrm2 (D.w i) + nrm2 (D.w (iA i))))
              + 4 * (D.M ^ 2 * m4) := by
          have hc : ∀ i : Fin 4, ((nrm2 (D.w i) + nrm2 (D.w (iA i))) * D.M * m3
                + D.M ^ 2 * m4)
              = (D.M * m3) * (nrm2 (D.w i) + nrm2 (D.w (iA i))) + (D.M ^ 2 * m4) :=
            fun i => by ring
          rw [Finset.sum_congr rfl (fun i _ => hc i), Finset.sum_add_distrib,
            ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            Fintype.card_fin]
          push_cast
          ring
        have hsumB : (∑ i : Fin 4, ((nrm2 (D.w i) + nrm2 (D.w (iB i))) * D.M * m3
                + D.M ^ 2 * m4))
            = D.M * m3 * (∑ i : Fin 4, (nrm2 (D.w i) + nrm2 (D.w (iB i))))
              + 4 * (D.M ^ 2 * m4) := by
          have hc : ∀ i : Fin 4, ((nrm2 (D.w i) + nrm2 (D.w (iB i))) * D.M * m3
                + D.M ^ 2 * m4)
              = (D.M * m3) * (nrm2 (D.w i) + nrm2 (D.w (iB i))) + (D.M ^ 2 * m4) :=
            fun i => by ring
          rw [Finset.sum_congr rfl (fun i _ => hc i), Finset.sum_add_distrib,
            ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            Fintype.card_fin]
          push_cast
          ring
        rw [Finset.sum_add_distrib, hsumA, hsumB]
        unfold T1
        ring
    _ = (C/2) * (D.M * T1 D * ((Real.sqrt α) ^ 3 * C3) + 8 * D.M ^ 2 * (α ^ 2 * C4)) := by
        rw [hm3, m3_scaling hα, hm4, m4_scaling hα]

/-- Claim (i): pointwise limit lim_{α→0⁺} E(α)[Φ]/α = ⟨W, K̃W⟩ -/
theorem heat_kernel_tendsto (D : FieldData) (hC : 0 ≤ C) :
    Filter.Tendsto (fun α => Egeom D C α / α - Kquad C D.w)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  set g : ℝ → ℝ := fun α =>
    (C/2) * (D.M * T1 D * (C3 * Real.sqrt α) + 8 * D.M ^ 2 * (C4 * α)) with hg
  have hgcont : Continuous g := by
    show Continuous fun α : ℝ =>
      (C/2) * (D.M * T1 D * (C3 * Real.sqrt α) + 8 * D.M ^ 2 * (C4 * α))
    fun_prop
  have hg0 : g 0 = 0 := by simp [hg, Real.sqrt_zero]
  have hgtend : Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    conv => rhs; rw [← hg0]
    exact hgcont.continuousWithinAt
  refine squeeze_zero_norm' ?_ hgtend
  filter_upwards [self_mem_nhdsWithin] with α hαmem
  have hα : 0 < α := hαmem
  rw [Real.norm_eq_abs]
  have h1 : Egeom D C α / α - Kquad C D.w = (Egeom D C α - α * Kquad C D.w) / α := by
    field_simp
  rw [h1, abs_div, abs_of_pos hα]
  have hbound := energy_error_bound D hC hα
  calc |Egeom D C α - α * Kquad C D.w| / α
      ≤ ((C/2) * (D.M * T1 D * ((Real.sqrt α) ^ 3 * C3) + 8 * D.M ^ 2 * (α ^ 2 * C4))) / α := by
        exact div_le_div_of_nonneg_right hbound hα.le
    _ = g α := by
        rw [hg]
        have hs3 : (Real.sqrt α) ^ 3 = Real.sqrt α * α := by
          have h2 : (Real.sqrt α) ^ 2 = α := Real.sq_sqrt hα.le
          calc (Real.sqrt α) ^ 3 = (Real.sqrt α) ^ 2 * Real.sqrt α := by ring
            _ = α * Real.sqrt α := by rw [h2]
            _ = Real.sqrt α * α := by ring
        rw [hs3]
        field_simp

/-- Claim (ii): on χAB-type gradient vectors, ⟨W,K̃W⟩ = −(C/2)‖W‖².
    χAB condition: w_{iA} = −J_A w_i (covector transformation + antisymmetry),
    i.e. w_{iA} = J_B w_i; likewise w_{iB} = J_A w_i. -/
theorem Kquad_chiAB (C : ℝ) (w : Fin 4 → ℝ × ℝ)
    (hA : ∀ i, w (iA i) = JB (w i)) (hB : ∀ i, w (iB i) = JA (w i)) :
    Kquad C w = -(C/2) * ∑ i : Fin 4, (nrm2 (w i)) ^ 2 := by
  unfold Kquad
  have hterm : ∀ i : Fin 4,
      dot (w i) (JA (w (iA i))) + dot (w i) (JB (w (iB i))) = -2 * (nrm2 (w i)) ^ 2 := by
    intro i
    rw [hA i, hB i]
    show dot (w i) (JA (JB (w i))) + dot (w i) (JB (JA (w i))) = -2 * (nrm2 (w i)) ^ 2
    simp only [JA, JB, dot, nrm2]
    rw [Real.sq_sqrt (by positivity)]
    ring
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hterm i]
  ring

/-- Energy is strictly negative on nonzero χAB gradient vectors: −(C/2)‖W‖² < 0 -/
theorem Kquad_chiAB_neg (C : ℝ) (w : Fin 4 → ℝ × ℝ) (hC : 0 < C)
    (hA : ∀ i, w (iA i) = JB (w i)) (hB : ∀ i, w (iB i) = JA (w i))
    (hne : ∃ i : Fin 4, w i ≠ 0) :
    Kquad C w < 0 := by
  rw [Kquad_chiAB C w hA hB]
  have hpos : 0 < ∑ i : Fin 4, (nrm2 (w i)) ^ 2 := by
    obtain ⟨i, hi⟩ := hne
    apply Finset.sum_pos' (fun j _ => by positivity)
    refine ⟨i, Finset.mem_univ i, ?_⟩
    have hw : w i ≠ 0 := hi
    have : nrm2 (w i) ≠ 0 := by
      intro hz
      apply hw
      unfold nrm2 at hz
      have h2 : (w i).1 ^ 2 + (w i).2 ^ 2 = 0 := by
        have hle := Real.sqrt_eq_zero'.mp hz
        exact le_antisymm hle (by positivity)
      have h1 : (w i).1 ^ 2 = 0 := le_antisymm
        (by linarith [sq_nonneg (w i).2, sq_nonneg (w i).1] :
          (w i).1 ^ 2 ≤ 0) (sq_nonneg _)
      have h2' : (w i).2 ^ 2 = 0 := le_antisymm
        (by linarith [sq_nonneg (w i).2, sq_nonneg (w i).1] :
          (w i).2 ^ 2 ≤ 0) (sq_nonneg _)
      ext
      · exact (pow_eq_zero_iff two_ne_zero).mp h1
      · exact (pow_eq_zero_iff two_ne_zero).mp h2'
    exact sq_pos_of_ne_zero this
  have : -(C/2) * ∑ i : Fin 4, (nrm2 (w i)) ^ 2 < 0 := by
    apply mul_neg_of_neg_of_pos
    · linarith
    · exact hpos
  exact this

/-- **Lemma 9.5C (main theorem)**: (i) pointwise limit + (ii) χAB eigenvalue
    inheritance (strictly negative) -/
theorem lemma_9_5C (D : FieldData) (hC : 0 < C) :
    (Filter.Tendsto (fun α => Egeom D C α / α) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Kquad C D.w)))
    ∧ ((∀ i, D.w (iA i) = JB (D.w i)) → (∀ i, D.w (iB i) = JA (D.w i)) →
      (∃ i : Fin 4, D.w i ≠ 0) → Kquad C D.w < 0) := by
  refine ⟨?_, ?_⟩
  · have h := heat_kernel_tendsto D hC.le
    have h2 : Filter.Tendsto (fun α => (Egeom D C α / α - Kquad C D.w) + Kquad C D.w)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 + Kquad C D.w)) :=
      h.add tendsto_const_nhds
    simp only [sub_add_cancel, zero_add] at h2
    exact h2
  · intro hA hB hne
    exact Kquad_chiAB_neg C D.w hC hA hB hne

end Energy

end RH95C


/- ## Axiom audit -/
section Audit
#print axioms RH95C.moment2
#print axioms RH95C.channel_main
#print axioms RH95C.channel_bound
#print axioms RH95C.energy_error_bound
#print axioms RH95C.heat_kernel_tendsto
#print axioms RH95C.Kquad_chiAB
#print axioms RH95C.Kquad_chiAB_neg
#print axioms RH95C.lemma_9_5C
end Audit

end
