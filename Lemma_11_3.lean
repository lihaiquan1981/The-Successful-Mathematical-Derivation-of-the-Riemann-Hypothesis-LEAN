/-
Li Haiquan
Jilin University of Chemical Technology, China
ORCID: https://orcid.org/0009-0000-7365-6535
Email: lihaiquan@jluct.edu.cn
-/

/-
Lemma 11.3 (Real-Axis Positivity Exclusion) — Formalization

Paper reference: "A Successful Mathematical Derivation of the Riemann
Hypothesis via Bidirectional Forward-Reverse Closure", paragraphs 973–996.

Mathematical content (§11.3 of the paper):
  ξ(s) = ½·s·(s−1)·π^(−s/2)·Γ(s/2)·ζ(s)  (i.e. ½·s·(s−1)·Λ(s), Λ = completedRiemannZeta)
  (i)   s ∈ (0,1): s(s−1) < 0 and ζ(s) < 0, negative times negative is positive,
        π^(−s/2) > 0, Γ(s/2) > 0 ⟹ ξ(s) > 0
  (ii)  s > 1: ζ(s) = Σ n^(−s) is termwise positive ⟹ ζ(s) > 0 ⟹ ξ(s) > 0
  (iii) ξ(s) = ξ(1−s) (functional equation) ⟹ the case s < 0 is covered by (ii)
  (iv)  g(w) := ξ(½ + √w) > 0 for all real w ≥ 0 (w ≠ ¼; w = ¼ corresponds to
        the removable points s ∈ {0,1})
  (v)   Critical-line lock: if (s − ½)² is a negative real, then Re s = ½,
        i.e. s = ½ ± i·√|w|

Boundary note: the "ζ strictly negative on (0,1)" needed in step (i) is what
the paper itself calls "combining known classical facts" (paragraph 976); this
file introduces it as the single explicit classical-input hypothesis `hζ`.
Everything else — including ζ > 0 for s > 1, the functional equation,
positivity on the three intervals, positivity of g(w), and the critical-line
lock — is machine-proved with zero sorry.
Axiom audit: all theorems depend only on [propext, Classical.choice, Quot.sound].
-/

import Mathlib

open Complex Filter Topology

namespace RH113

/-! ## Definition of the ξ function and its functional equation -/

/-- The ξ function of §11.3: `ξ(s) = (s(s−1)/2)·Λ(s)`,
where `Λ = completedRiemannZeta` (i.e. `π^(−s/2)·Γ(s/2)·ζ(s)`). -/
noncomputable def xiFn (s : ℂ) : ℂ := (s * (s - 1) / 2) * completedRiemannZeta s

/-- The functional equation of ξ (paragraph 981): `ξ(1−s) = ξ(s)`. -/
theorem xiFn_one_sub (s : ℂ) : xiFn (1 - s) = xiFn s := by
  unfold xiFn
  rw [completedRiemannZeta_one_sub]
  ring

/-! ## Strict positivity of ζ for s > 1 (machine proof, termwise positive) -/

/-- Conjugate symmetry of ζ on the real axis: ζ of a real input is real. -/
lemma zeta_ofReal_im (x : ℝ) : (riemannZeta (x : ℂ)).im = 0 := by
  have h := riemannZeta_conj (x : ℂ)
  rw [conj_ofReal] at h
  exact (conj_eq_iff_im.mp h.symm)

/-- For s > 1, the series of ζ is termwise a positive real. -/
lemma zeta_series_term_ofReal (x : ℝ) (n : ℕ) :
    (1 / ((n : ℂ) + 1) ^ (x : ℂ)).re = ((n : ℝ) + 1) ^ (-x) := by
  have e1 : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [e1, ← ofReal_cpow (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) x, one_div,
    ← ofReal_inv, ofReal_re, ← Real.rpow_neg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]

/-- For real s > 1, `ζ(s) > 0`: the series positivity argument of paragraph 980. -/
theorem zeta_re_pos_of_one_lt {x : ℝ} (hx : 1 < x) : 0 < (riemannZeta (x : ℂ)).re := by
  have hre : 1 < (x : ℂ).re := by simpa using hx
  have hsumm : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ (x : ℂ)) := by
    have h := (Complex.summable_one_div_nat_cpow).mpr hre
    have h' := (summable_nat_add_iff 1).mpr h
    refine h'.congr (fun n => by push_cast; ring)
  have hsumr : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-x)) := by
    have h2 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ x) :=
      (Real.summable_one_div_nat_rpow).mpr hx
    have h3 := (summable_nat_add_iff 1).mpr h2
    refine h3.congr (fun n => ?_)
    push_cast
    rw [one_div, ← Real.rpow_neg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre]
  have e := reCLM.map_tsum hsumm
  simp only [reCLM_apply] at e
  rw [e, tsum_congr (fun n => zeta_series_term_ofReal x n)]
  refine hsumr.tsum_pos (fun n => Real.rpow_nonneg (by positivity) _) 0 ?_
  simp

/-! ## The real-valued ξ and its positivity -/

/-- Real-valued ξ: `xiReal x = (x(x−1)/2)·π^(−x/2)·Γ(x/2)·Re ζ(x)`. -/
noncomputable def xiReal (x : ℝ) : ℝ :=
  (x * (x - 1) / 2) * Real.pi ^ (-x / 2) * Real.Gamma (x / 2) * (riemannZeta (x : ℂ)).re

/-- Bridge between complex ξ and real ξ (for x > 0, `Gammaℝ x ≠ 0`, so the
formula is legitimate). -/
lemma xiFn_ofReal_of_pos {x : ℝ} (hx : 0 < x) : xiFn (x : ℂ) = ((xiReal x : ℝ) : ℂ) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hG0 : Gammaℝ (x : ℂ) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simpa using hx)
  have hL : completedRiemannZeta (x : ℂ) = riemannZeta (x : ℂ) * Gammaℝ (x : ℂ) := by
    rw [riemannZeta_def_of_ne_zero hx0]
    exact (div_mul_cancel₀ _ hG0).symm
  have hGR : Gammaℝ (x : ℂ) =
      (((Real.pi ^ (-x / 2)) * Real.Gamma (x / 2) : ℝ) : ℂ) := by
    rw [Gammaℝ_def]
    have e1 : (-(x : ℂ) / 2) = ((-x / 2 : ℝ) : ℂ) := by push_cast; ring
    have e2 : ((x : ℂ) / 2) = ((x / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e2, Gamma_ofReal, ← ofReal_cpow Real.pi_pos.le (-x / 2), ← ofReal_mul]
  have hζ : riemannZeta (x : ℂ) = (((riemannZeta (x : ℂ)).re : ℝ) : ℂ) := by
    have h := zeta_ofReal_im x
    rw [← Complex.re_add_im (riemannZeta (x : ℂ)), h]
    simp
  unfold xiFn xiReal
  rw [hL, hGR]
  conv_lhs => rw [hζ]
  push_cast
  ring

/-- The interval (0,1): negative times negative is positive (paragraph 978). -/
theorem xiReal_pos_of_Ioo
    (hζ : ∀ x : ℝ, 0 < x → x < 1 → (riemannZeta (x : ℂ)).re < 0)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : 0 < xiReal x := by
  have h1 : x * (x - 1) / 2 < 0 := by
    have h := mul_neg_of_pos_of_neg hx0 (by linarith : x - 1 < 0)
    linarith
  have h2 : (0 : ℝ) < Real.pi ^ (-x / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  have h3 : (0 : ℝ) < Real.Gamma (x / 2) := Real.Gamma_pos_of_pos (by linarith)
  have h4 : (riemannZeta (x : ℂ)).re < 0 := hζ x hx0 hx1
  have h14 : (0 : ℝ) < (x * (x - 1) / 2) * (riemannZeta (x : ℂ)).re :=
    mul_pos_of_neg_of_neg h1 h4
  have e : (x * (x - 1) / 2) * Real.pi ^ (-x / 2) * Real.Gamma (x / 2) *
      (riemannZeta (x : ℂ)).re =
      ((x * (x - 1) / 2) * (riemannZeta (x : ℂ)).re) * Real.pi ^ (-x / 2) *
      Real.Gamma (x / 2) := by ring
  unfold xiReal
  rw [e]
  exact mul_pos (mul_pos h14 h2) h3

/-- The interval x > 1: all factors are positive (paragraph 980). -/
theorem xiReal_pos_of_one_lt {x : ℝ} (hx : 1 < x) : 0 < xiReal x := by
  have h1 : (0 : ℝ) < x * (x - 1) / 2 := by
    have h := mul_pos (zero_lt_one.trans hx) (by linarith : (0 : ℝ) < x - 1)
    linarith
  have h2 : (0 : ℝ) < Real.pi ^ (-x / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  have h3 : (0 : ℝ) < Real.Gamma (x / 2) := Real.Gamma_pos_of_pos (by linarith)
  have h4 : (0 : ℝ) < (riemannZeta (x : ℂ)).re := zeta_re_pos_of_one_lt hx
  exact mul_pos (mul_pos (mul_pos h1 h2) h3) h4

/-- The interval x < 0: reduced to 1−x > 1 via the functional equation
(paragraph 981). -/
theorem xiFn_pos_ofReal_of_neg {x : ℝ} (hx : x < 0) :
    xiFn (x : ℂ) = (((xiReal (1 - x)) : ℝ) : ℂ) ∧ 0 < xiReal (1 - x) := by
  have h1x : (1 : ℝ) < 1 - x := by linarith
  have hpos : (0 : ℝ) < xiReal (1 - x) := xiReal_pos_of_one_lt h1x
  have e : xiFn (x : ℂ) = xiFn ((1 - x : ℝ) : ℂ) := by
    have h := xiFn_one_sub (x : ℂ)
    have e2 : ((1 - x : ℝ) : ℂ) = 1 - (x : ℂ) := by push_cast; ring
    rw [e2, h]
  exact ⟨e.trans (xiFn_ofReal_of_pos (by linarith : (0 : ℝ) < 1 - x)), hpos⟩

/-! ## Lemma 11.3, main theorem -/

/-- **Lemma 11.3 (Real-axis positivity exclusion)**: for real x ∉ {0, 1},
ξ(x) is a strictly positive real number.

The hypothesis `hζ` is the single classical input (paragraph 976 of the paper:
"combining known classical facts"); the case x < 0 is covered via the
functional equation, x ∈ (0,1) by negative-times-negative, x > 1 by termwise
positivity of the series. -/
theorem lemma_11_3
    (hζ : ∀ x : ℝ, 0 < x → x < 1 → (riemannZeta (x : ℂ)).re < 0)
    {x : ℝ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    (0 : ℝ) < (xiFn (x : ℂ)).re ∧ (xiFn (x : ℂ)).im = 0 := by
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · obtain ⟨e, hp⟩ := xiFn_pos_ofReal_of_neg hneg
    rw [e]
    exact ⟨by simpa using hp, by simp⟩
  · rcases lt_or_gt_of_ne hx1 with hlt | hgt
    · rw [xiFn_ofReal_of_pos hpos]
      exact ⟨by simpa using xiReal_pos_of_Ioo hζ hpos hlt, by simp⟩
    · rw [xiFn_ofReal_of_pos hpos]
      exact ⟨by simpa using xiReal_pos_of_one_lt hgt, by simp⟩

/-- Corollary (used in §12.1 of the paper): ξ has no zeros on the real axis
(except the removable points 0, 1). -/
theorem xiFn_ne_zero_ofReal
    (hζ : ∀ x : ℝ, 0 < x → x < 1 → (riemannZeta (x : ℂ)).re < 0)
    {x : ℝ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) : xiFn (x : ℂ) ≠ 0 := by
  obtain ⟨hpos, -⟩ := lemma_11_3 hζ hx0 hx1
  intro h
  rw [h] at hpos
  simp at hpos

/-! ## Positivity of g(w) and the critical-line lock (paragraphs 982–996) -/

/-- The paper's `g(w) = ξ(½ + √w)` (real w ≥ 0). -/
noncomputable def gFn (w : ℝ) : ℝ := xiReal (1 / 2 + Real.sqrt w)

/-- g(w) > 0 for all real w ≥ 0, w ≠ ¼ (paragraphs 982–993).
w = ¼ corresponds to the removable points s ∈ {0,1} (the true ξ(0) = ξ(1) = ½ > 0,
but the factored form involves a pole cancellation of Γ/ζ there and is not
covered by this factorization). -/
theorem gFn_pos
    (hζ : ∀ x : ℝ, 0 < x → x < 1 → (riemannZeta (x : ℂ)).re < 0)
    {w : ℝ} (hw : 0 ≤ w) (hwq : w ≠ 1 / 4) : 0 < gFn w := by
  unfold gFn
  set r := Real.sqrt w with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg w
  have hx0 : (0 : ℝ) < 1 / 2 + r := by linarith
  rcases eq_or_ne r (1 / 2) with rh | rh
  · exfalso
    apply hwq
    have hwsq : w = r ^ 2 := (Real.sq_sqrt hw).symm
    rw [hwsq, rh]
    norm_num
  · rcases lt_or_gt_of_ne rh with hlt | hgt
    · exact xiReal_pos_of_Ioo hζ hx0 (by linarith)
    · exact xiReal_pos_of_one_lt (by linarith)

/-- Zero exclusion: if (s − ½)² is a nonnegative real w (w ≠ ¼), then ξ(s) ≠ 0.
(Paragraphs 994–995: real zeros of g must lie at w < 0.) -/
theorem xiFn_ne_zero_of_w_nonneg
    (hζ : ∀ x : ℝ, 0 < x → x < 1 → (riemannZeta (x : ℂ)).re < 0)
    {s : ℂ} {w : ℝ} (hw : (s - 1 / 2) ^ 2 = (w : ℂ)) (hw0 : 0 ≤ w) (hwq : w ≠ 1 / 4) :
    xiFn s ≠ 0 := by
  set r := Real.sqrt w with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg w
  have hsq : (w : ℂ) = (r : ℂ) ^ 2 := by
    rw [sq, ← ofReal_mul, ← sq, Real.sq_sqrt hw0]
  rw [hsq] at hw
  have hcases : s - 1 / 2 = (r : ℂ) ∨ s - 1 / 2 = -(r : ℂ) := by
    have hfact : (s - 1 / 2 - (r : ℂ)) * (s - 1 / 2 + (r : ℂ)) = 0 := by
      linear_combination hw
    rcases mul_eq_zero.mp hfact with h1 | h2
    · exact Or.inl (eq_of_sub_eq_zero h1)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h2)
  have hw_of_half : r = 1 / 2 → w = 1 / 4 := by
    intro hr2
    have hwsq : w = r ^ 2 := (Real.sq_sqrt hw0).symm
    rw [hwsq, hr2]
    norm_num
  rcases hcases with h1 | h2
  · have hx : s = ((1 / 2 + r : ℝ) : ℂ) := by
      have hs : s = (s - 1 / 2) + 1 / 2 := by ring
      rw [hs, h1]
      push_cast
      ring
    have hx0' : (1 / 2 : ℝ) + r ≠ 0 := by linarith
    have hx1' : (1 / 2 : ℝ) + r ≠ 1 := by
      intro h
      exact hwq (hw_of_half (by linarith))
    rw [hx]
    exact xiFn_ne_zero_ofReal hζ hx0' hx1'
  · have hx : s = ((1 / 2 - r : ℝ) : ℂ) := by
      have hs : s = (s - 1 / 2) + 1 / 2 := by ring
      rw [hs, h2]
      push_cast
      ring
    have hx0' : (1 / 2 : ℝ) - r ≠ 0 := by
      intro h
      exact hwq (hw_of_half (by linarith))
    have hx1' : (1 / 2 : ℝ) - r ≠ 1 := by
      intro h
      linarith
    rw [hx]
    exact xiFn_ne_zero_ofReal hζ hx0' hx1'

/-- **Critical-line lock** (paragraphs 994–996): if (s − ½)² equals some
negative real w, then `Re s = ½`, i.e. `s = ½ ± i·√|w|` lies on the critical
line. -/
theorem critical_line_lock {s : ℂ} {w : ℝ} (hw : (s - 1 / 2) ^ 2 = (w : ℂ)) (hwneg : w < 0) :
    s.re = 1 / 2 := by
  have hdecomp : s - 1 / 2 = ((s.re - 1 / 2 : ℝ) : ℂ) + (s.im : ℂ) * Complex.I := by
    simp [Complex.ext_iff]
  have key : (s - 1 / 2) ^ 2 =
      (((s.re - 1 / 2) ^ 2 - s.im ^ 2 : ℝ) : ℂ) +
      ((2 * (s.re - 1 / 2) * s.im : ℝ) : ℂ) * Complex.I := by
    rw [hdecomp, add_sq, mul_pow, Complex.I_sq]
    push_cast
    ring
  rw [key] at hw
  have h2ab : (2 : ℝ) * (s.re - 1 / 2) * s.im = 0 := by
    have h := congrArg Complex.im hw
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add] at h
    exact h
  have hre : (s.re - 1 / 2) ^ 2 - s.im ^ 2 = w := by
    have h := congrArg Complex.re hw
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, sub_zero] at h
    exact h
  rcases mul_eq_zero.mp h2ab with h1 | h2
  · have ha : s.re - 1 / 2 = 0 := by
      rcases mul_eq_zero.mp h1 with h3 | h3
      · norm_num at h3
      · exact h3
    linarith
  · exfalso
    rw [h2] at hre
    nlinarith [sq_nonneg (s.re - 1 / 2)]

end RH113

/-! ## Axiom audit -/

section Audit

#print axioms RH113.xiFn_one_sub
#print axioms RH113.zeta_re_pos_of_one_lt
#print axioms RH113.xiFn_ofReal_of_pos
#print axioms RH113.xiReal_pos_of_Ioo
#print axioms RH113.xiReal_pos_of_one_lt
#print axioms RH113.xiFn_pos_ofReal_of_neg
#print axioms RH113.lemma_11_3
#print axioms RH113.xiFn_ne_zero_ofReal
#print axioms RH113.gFn_pos
#print axioms RH113.xiFn_ne_zero_of_w_nonneg
#print axioms RH113.critical_line_lock

end Audit
