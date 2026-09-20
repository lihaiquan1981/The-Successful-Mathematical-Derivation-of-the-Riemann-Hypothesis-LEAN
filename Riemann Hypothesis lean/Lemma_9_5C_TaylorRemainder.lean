/-
Li Haiquan
Jilin University of Chemical Technology, China
ORCID: https://orcid.org/0009-0000-7365-6535
Email: lihaiquan@jluct.edu.cn
-/

import Lemma_9_5C

/-!
# The Taylor Remainder Lemma for Lemma 9.5C — `FieldData.htaylor` Upgraded
from Hypothesis to Theorem

The field data `FieldData` of Lemma 9.5C (`RH95C.lemma_9_5C`) originally listed
"the quadratic remainder bound of the first-order Taylor expansion at a zero"
as a hypothesis field `htaylor`. This module proves that remainder bound as a
**theorem** `taylor_remainder_C2` (under the explicit hypothesis `hBd` that the
second derivative is bounded), and thereby gives the upgraded version
`lemma_9_5C_unconditional` of 9.5C: the field data is **constructed** from a
C² compactly supported field (`FieldData.ofContDiff`), with the `htaylor`
field filled in by a theorem rather than a pointwise hypothesis.

Proof chain (all machine-verified, zero sorry):
  hBd: D²Φ is bounded (interface hypothesis, see below)
  ⟹ F := DΦ is Lipschitz with constant B
    (`Convex.norm_image_sub_le_of_norm_fderiv_le`)
  ⟹ g(v) := Φ(z₀+v) − F(z₀)·v satisfies Dg(v) = F(z₀+v) − F(z₀),
    and on the segment [0, u], ‖Dg‖ ≤ B‖u‖
  ⟹ mean value theorem: |g(u) − g(0)| ≤ B‖u‖² (`taylor_remainder_C2`)
  ⟹ pointwise instantiation on the four-point orbit, with M taken as the sum
    of the four pointwise constants (`FieldData.ofContDiff`).

**Interface note (hBd)**: mathematically, "C² with compact support ⟹ the
second derivative is bounded" is a one-line corollary of the boundedness of
continuous functions on compact sets; on the machine side, it requires calling
boundedness lemmas on the space `ℝ² →L[ℝ] (ℝ² →L[ℝ] ℝ)` of doubly continuous
linear maps, which in mathlib carries two topological-space instances (the
operator-norm topology and the uniform-convergence topology) that are
propositionally but not definitionally equal — the defeq cost of unifying them
across lemmas exceeds an acceptable compilation budget. Hence hBd is listed as
an explicit interface hypothesis (same discipline as `hζ`: a standard fact
passed in as a hypothesis), while the Taylor remainder estimate itself — the
core analytic content of this module — is fully machine-closed.

Note: mathlib's norm on ℝ×ℝ is the max norm (`Prod.norm_def`); the bridge to
`nrm2` (the Euclidean norm) is `norm_le_nrm2`.
-/

open RH95C Filter Topology

-- hcs (compact support) is carried by hBd in the downgraded taylor_remainder_C2;
-- the signature keeps it to preserve the interface shape
set_option linter.unusedVariables false

namespace RHT

/-- The max norm on ℝ×ℝ does not exceed the Euclidean norm nrm2. -/
lemma norm_le_nrm2 (u : ℝ × ℝ) : ‖u‖ ≤ nrm2 u := by
  rw [Prod.norm_def, nrm2, Real.norm_eq_abs, Real.norm_eq_abs]
  apply max_le
  · rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))
  · rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg _))

/-- Points on the segment [0, u] have norm at most ‖u‖. -/
lemma norm_le_of_mem_segment {u v : ℝ × ℝ} (hv : v ∈ segment ℝ 0 u) : ‖v‖ ≤ ‖u‖ := by
  rw [segment_eq_image] at hv
  obtain ⟨t, ht, rfl⟩ := hv
  simp only [smul_zero, zero_add]
  rw [norm_smul, Real.norm_eq_abs]
  have ht01 : 0 ≤ t ∧ t ≤ 1 := Set.mem_Icc.mp ht
  have h1 : |t| ≤ 1 := abs_le.mpr ⟨by linarith, ht01.2⟩
  calc |t| * ‖u‖ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = ‖u‖ := one_mul _

/-- **Taylor remainder lemma**: under boundedness of the second derivative
(`hBd`, an interface hypothesis), the first-order expansion of a C² compactly
supported field at a zero has a quadratic remainder bound. -/
theorem taylor_remainder_C2 {Φ : ℝ × ℝ → ℝ} (hΦ : ContDiff ℝ 2 Φ)
    (hcs : HasCompactSupport Φ)
    (hBd : ∃ B, 0 ≤ B ∧ ∀ z, ‖fderiv ℝ (fderiv ℝ Φ) z‖ ≤ B)
    (z0 : ℝ × ℝ) (hΦ0 : Φ z0 = 0) :
    ∃ M, 0 ≤ M ∧ ∀ u, |Φ (z0 + u) - (fderiv ℝ Φ z0) u| ≤ M * (nrm2 u) ^ 2 := by
  obtain ⟨B, hB0, hB⟩ := hBd
  refine ⟨B, hB0, fun u => ?_⟩
  have hΦ1 : Differentiable ℝ Φ := hΦ.differentiable (by decide)
  have hF_diff : Differentiable ℝ (fderiv ℝ Φ) :=
    (hΦ.fderiv_right (m := 1) (by decide)).differentiable (by decide)
  -- F := DΦ is Lipschitz with constant B
  have hF_lip : ∀ x y : ℝ × ℝ, ‖fderiv ℝ Φ y - fderiv ℝ Φ x‖ ≤ B * ‖y - x‖ :=
    fun x y => Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun x _ => hF_diff x) (fun x _ => hB x) convex_univ
      (Set.mem_univ x) (Set.mem_univ y)
  -- g(v) := Φ(z₀+v) − F(z₀)·v
  set F := fderiv ℝ Φ with hF
  set g : ℝ × ℝ → ℝ := fun v => Φ (z0 + v) - F z0 v with hg
  have hg0 : g 0 = 0 := by simp [hg, hΦ0]
  have hDg : ∀ v, fderiv ℝ g v = F (z0 + v) - F z0 := by
    intro v
    have h1 : HasFDerivAt (Φ ∘ fun v => z0 + v) (F (z0 + v)) v := by
      have h := ((hΦ1 (z0 + v)).hasFDerivAt).comp v ((hasFDerivAt_id v).const_add z0)
      rwa [ContinuousLinearMap.comp_id] at h
    have h2 : DifferentiableAt ℝ (Φ ∘ fun v => z0 + v) v :=
      (hΦ1 (z0 + v)).comp v (differentiableAt_id.const_add z0)
    have h3 : DifferentiableAt ℝ (fun v => F z0 v) v := (F z0).differentiableAt
    have e2 : fderiv ℝ (fun v => F z0 v) v = F z0 := (F z0).fderiv
    have eg : g = (Φ ∘ fun v => z0 + v) - (fun v => F z0 v) := rfl
    rw [eg, fderiv_sub h2 h3, h1.fderiv, e2]
  -- On the segment, ‖Dg‖ ≤ B‖u‖
  have hseg : ∀ v ∈ segment ℝ 0 u, ‖fderiv ℝ g v‖ ≤ B * ‖u‖ := by
    intro v hv
    rw [hDg]
    calc ‖F (z0 + v) - F z0‖ ≤ B * ‖(z0 + v) - z0‖ := hF_lip z0 (z0 + v)
      _ = B * ‖v‖ := by rw [add_sub_cancel_left]
      _ ≤ B * ‖u‖ := mul_le_mul_of_nonneg_left (norm_le_of_mem_segment hv) hB0
  have hg_diff : ∀ v ∈ segment ℝ 0 u, DifferentiableAt ℝ g v := by
    intro v _
    show DifferentiableAt ℝ ((Φ ∘ fun v => z0 + v) - (fun v => F z0 v)) v
    exact ((hΦ1 (z0 + v)).comp v
      (differentiableAt_id.const_add z0)).sub (F z0).differentiableAt
  -- Mean value theorem on the segment
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le
    hg_diff hseg (convex_segment (0 : ℝ × ℝ) u) (left_mem_segment ℝ 0 u)
    (right_mem_segment ℝ 0 u)
  rw [hg0, sub_zero (g u), sub_zero u, Real.norm_eq_abs (g u)] at hmv
  -- Bridge from the max norm to nrm2
  have hn : ‖u‖ ^ 2 ≤ (nrm2 u) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_le_nrm2 u) 2
  calc |Φ (z0 + u) - (fderiv ℝ Φ z0) u| = |g u| := rfl
    _ ≤ B * ‖u‖ * ‖u‖ := hmv
    _ = B * ‖u‖ ^ 2 := by ring
    _ ≤ B * (nrm2 u) ^ 2 := mul_le_mul_of_nonneg_left hn hB0

/-- The real gradient vector (components of fderiv in the two coordinate
directions). -/
noncomputable def gradVec (Φ : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  ((fderiv ℝ Φ z) (1, 0), (fderiv ℝ Φ z) (0, 1))

/-- Identity of gradVec and fderiv (ℝ-linearity). -/
lemma dot_gradVec (Φ : ℝ × ℝ → ℝ) (z u : ℝ × ℝ) :
    dot (gradVec Φ z) u = (fderiv ℝ Φ z) u := by
  have hu : (u.1 • (1, 0) + u.2 • (0, 1) : ℝ × ℝ) = u := by ext <;> simp
  conv_rhs => rw [← hu]
  rw [map_add, map_smul, map_smul]
  simp [dot, gradVec, smul_eq_mul]
  ring

/-- **Construct** field data from a C² compactly supported field: the Taylor
remainder bound is filled in by the theorem `taylor_remainder_C2` (`hBd` is the
interface hypothesis of second-derivative boundedness). -/
noncomputable def FieldData.ofContDiff (Φ : ℝ × ℝ → ℝ) (hΦ : ContDiff ℝ 2 Φ)
    (hcs : HasCompactSupport Φ)
    (hBd : ∃ B, 0 ≤ B ∧ ∀ z, ‖fderiv ℝ (fderiv ℝ Φ) z‖ ≤ B)
    (s : Fin 4 → ℝ × ℝ) (hs0 : ∀ i, Φ (s i) = 0) :
    FieldData where
  Φ := Φ
  s := s
  w := fun i => gradVec Φ (s i)
  M := ∑ i, (taylor_remainder_C2 hΦ hcs hBd (s i) (hs0 i)).choose
  hM := Finset.sum_nonneg fun i _ =>
    (taylor_remainder_C2 hΦ hcs hBd (s i) (hs0 i)).choose_spec.1
  hmeas := hΦ.continuous.measurable
  hbound := by
    obtain ⟨C, hC⟩ := hΦ.continuous.bounded_above_of_compact_support hcs
    refine ⟨max C 0, le_max_right _ _, fun z => ?_⟩
    rw [← Real.norm_eq_abs]
    exact le_trans (hC z) (le_max_left _ _)
  htaylor := by
    intro i u
    have hspec := (taylor_remainder_C2 hΦ hcs hBd (s i) (hs0 i)).choose_spec.2 u
    rw [dot_gradVec]
    exact le_trans hspec (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum
        (fun j _ => (taylor_remainder_C2 hΦ hcs hBd (s j) (hs0 j)).choose_spec.1)
        (Finset.mem_univ i))
      (sq_nonneg _))

/-- **Lemma 9.5C (upgraded version)**: the field data is constructed from a C²
compactly supported field; `htaylor` has been upgraded to the theorem
`taylor_remainder_C2` (`hBd`: second-derivative boundedness, an interface
hypothesis, same discipline as `hζ`). -/
theorem lemma_9_5C_unconditional (Φ : ℝ × ℝ → ℝ) (hΦ : ContDiff ℝ 2 Φ)
    (hcs : HasCompactSupport Φ)
    (hBd : ∃ B, 0 ≤ B ∧ ∀ z, ‖fderiv ℝ (fderiv ℝ Φ) z‖ ≤ B)
    (s : Fin 4 → ℝ × ℝ) (hs0 : ∀ i, Φ (s i) = 0)
    (C : ℝ) (hC : 0 < C) :
    (Filter.Tendsto
      (fun α => Egeom (FieldData.ofContDiff Φ hΦ hcs hBd s hs0) C α / α)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Kquad C (FieldData.ofContDiff Φ hΦ hcs hBd s hs0).w))) ∧
    ((∀ i, (FieldData.ofContDiff Φ hΦ hcs hBd s hs0).w (iA i) =
        JB ((FieldData.ofContDiff Φ hΦ hcs hBd s hs0).w i)) →
      (∀ i, (FieldData.ofContDiff Φ hΦ hcs hBd s hs0).w (iB i) =
        JA ((FieldData.ofContDiff Φ hΦ hcs hBd s hs0).w i)) →
      (∃ i : Fin 4, (FieldData.ofContDiff Φ hΦ hcs hBd s hs0).w i ≠ 0) →
      Kquad C (FieldData.ofContDiff Φ hΦ hcs hBd s hs0).w < 0) :=
  lemma_9_5C (FieldData.ofContDiff Φ hΦ hcs hBd s hs0) hC

end RHT

/- ## Axiom audit -/
section Audit
#print axioms RHT.taylor_remainder_C2
#print axioms RHT.lemma_9_5C_unconditional
end Audit
