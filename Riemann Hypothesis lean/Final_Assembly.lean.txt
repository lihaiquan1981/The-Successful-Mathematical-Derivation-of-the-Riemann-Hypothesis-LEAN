/-
Li Haiquan
Jilin University of Chemical Technology, China
ORCID: https://orcid.org/0009-0000-7365-6535
Email: lihaiquan@jluct.edu.cn
-/

import Theorem_9_5_Closure
import Lemma_11_3

/-!
# Final Assembly — Endpoint of the Machine-Verification Chain for the
Riemann Hypothesis

Paper reference: "A Successful Mathematical Derivation of the Riemann
Hypothesis via Bidirectional Forward-Reverse Closure".

This file closes the two delivered machine-proof chains into a single master
theorem:

  Chain one (non-real zero exclusion):
    9.3A dimension reduction → 9.4 non-degenerate gradient → 9.5C heat-kernel
    negative energy → unitarity contradiction
    ⇒ `theorem_10_final`: for f satisfying the gate hypotheses, any zero with
    σ ≠ 1/2 must have t = 0.

  Chain two (real-axis positivity exclusion):
    Lemma 11.3 ⇒ `xiFn_ne_zero_ofReal`: ξ has no zeros on the real axis
    (except the removable points 0, 1).

  Assembly:
    A. `RH_general`: general form (dichotomy of zero locations for abstract f).
    B. `RH_xi`: the Riemann Hypothesis — the zeros (outside 0, 1) of an entire
       realization g of ξ all lie on Re s = 1/2.

Explicit hypothesis list (nothing else is assumed; no sorry):
  · the per-function unitarity premise `SatisfiesUnitarity C g` (C > 0) —
    exactly the premise of the paper's Theorem 9.5 ("for any f ∈ ℱ satisfying
    mother-equation unitarity, i.e. whose perturbation energy satisfies the
    unitarity axiom ΔE > 0"); the paper's final conclusion is stated "in the
    intersection of two conditions — the mother-equation unitarity axiom and
    the real-axis positivity of ξ" (paper, main-text Part 9, Step 8), which
    these two hypotheses mirror one-to-one;
  · the classical input `hζ`: ζ strictly negative on (0,1) (paragraph 976 of
    the paper: "combining known classical facts");
  · the four gate conditions on g: entireness, double-reflection symmetry,
    simplicity of zeros, pointwise agreement with xiFn outside 0, 1.
    The supporting fact on the xiFn side, `xiFn_differentiableAt`
    (differentiable outside 0, 1), is machine-proved in this file;
    the functional equation `xiFn_one_sub` was machine-proved in Lemma_11_3.
-/

open Complex
open RH95C RH95U RH94 RH95Final RH113

namespace RHFinal

/-- Local differentiability of ξ outside 0, 1 (machine proof).
At 0 and 1, the pole of Λ cancels the zero of the factor s(s−1)/2 — removable
points; the values of `xiFn` at these two points are artifacts of the
multiplicative definition acting on mathlib junk values, not mathematical
content. -/
theorem xiFn_differentiableAt {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ xiFn s := by
  unfold xiFn
  exact DifferentiableAt.mul (by fun_prop) (differentiableAt_completedZeta hs0 hs1)

/-- **Final Assembly A (general form)**: for a function f satisfying the four
explicit gate hypotheses, all zeros lie on the critical line Re s = 1/2 or on
the real axis (the dichotomy formulation of Theorem 10). -/
theorem RH_general (C : ℝ) (hC : 0 < C)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f (1 - s) = f s) (h_conj : ∀ s, f (star s) = star (f s))
    (hsimple : ∀ σ t : ℝ, f (↑σ + Complex.I * ↑t) = 0 →
      deriv f (↑σ + Complex.I * ↑t) ≠ 0)
    (hunit : SatisfiesUnitarity C f)
    {σ t : ℝ} (hz : f (↑σ + Complex.I * ↑t) = 0) :
    σ = 1 / 2 ∨ t = 0 := by
  by_cases hσ : σ = 1 / 2
  · exact Or.inl hσ
  · exact Or.inr (theorem_10_final C hC f hf h_sym h_conj hsimple hunit σ t hz hσ)

/-- **Final Assembly B (the Riemann Hypothesis)**:
Let `g` be an entire realization of ξ (pointwise equal to `xiFn` outside 0, 1),
satisfying the double-reflection symmetry and the simplicity-of-zeros gate;
then under the unitarity axiom and the single classical input `hζ`,
every zero s ∉ {0, 1} of g satisfies Re s = 1/2.

Proof structure:
  · If Im s = 0 (real-zero candidate): `hg_eq` reduces g to xiFn, and
    Lemma 11.3 (`xiFn_ne_zero_ofReal`) excludes it directly;
  · If Im s ≠ 0 and Re s ≠ 1/2: Theorem 10 closed-loop (`theorem_10_final`)
    forces Im s = 0 — contradiction. -/
theorem RH_xi (C : ℝ) (hC : 0 < C)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (hunit : SatisfiesUnitarity C g)
    (hζ : ∀ x : ℝ, 0 < x → x < 1 → (riemannZeta (x : ℂ)).re < 0)
    (hg_eq : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → g s = xiFn s)
    (hg_sym : ∀ s, g (1 - s) = g s) (hg_conj : ∀ s, g (star s) = star (g s))
    (hg_simple : ∀ σ t : ℝ, g (↑σ + Complex.I * ↑t) = 0 →
      deriv g (↑σ + Complex.I * ↑t) ≠ 0)
    {s : ℂ} (hz : g s = 0) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    s.re = 1 / 2 := by
  by_cases hre : s.re = 1 / 2
  · exact hre
  · exfalso
    by_cases him : s.im = 0
    · -- Real zero: excluded by Lemma 11.3
      have hs : s = (s.re : ℂ) := by
        have h := Complex.re_add_im s
        rw [him] at h
        simp at h
        exact h.symm
      have hx0 : s.re ≠ 0 := by
        intro h
        apply hs0
        rw [hs, h]
        simp
      have hx1 : s.re ≠ 1 := by
        intro h
        apply hs1
        rw [hs, h]
        simp
      rw [hs, hg_eq _ (by exact_mod_cast hx0) (by exact_mod_cast hx1)] at hz
      exact xiFn_ne_zero_ofReal hζ hx0 hx1 hz
    · -- Non-real zero with σ ≠ 1/2: the unitarity closed loop forces t = 0,
      -- contradiction
      have hz' : g (↑s.re + Complex.I * ↑s.im) = 0 := by
        rw [mul_comm, Complex.re_add_im]
        exact hz
      have h10 := theorem_10_final C hC g hg hg_sym hg_conj hg_simple hunit s.re s.im hz' hre
      exact him h10

/-- Equivalent packaging of the assembly corollary: the zero set of g is
contained in  critical line ∪ {0, 1}. -/
theorem RH_xi_zeros (C : ℝ) (hC : 0 < C)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (hunit : SatisfiesUnitarity C g)
    (hζ : ∀ x : ℝ, 0 < x → x < 1 → (riemannZeta (x : ℂ)).re < 0)
    (hg_eq : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → g s = xiFn s)
    (hg_sym : ∀ s, g (1 - s) = g s) (hg_conj : ∀ s, g (star s) = star (g s))
    (hg_simple : ∀ σ t : ℝ, g (↑σ + Complex.I * ↑t) = 0 →
      deriv g (↑σ + Complex.I * ↑t) ≠ 0)
    {s : ℂ} (hz : g s = 0) :
    s.re = 1 / 2 ∨ s = 0 ∨ s = 1 := by
  by_cases hs0 : s = 0
  · exact Or.inr (Or.inl hs0)
  · by_cases hs1 : s = 1
    · exact Or.inr (Or.inr hs1)
    · exact Or.inl (RH_xi C hC g hg hunit hζ hg_eq hg_sym hg_conj hg_simple hz hs0 hs1)

end RHFinal

/- ## Axiom audit -/
section Audit
#print axioms RHFinal.xiFn_differentiableAt
#print axioms RHFinal.RH_general
#print axioms RHFinal.RH_xi
#print axioms RHFinal.RH_xi_zeros
end Audit
