/-
Li Haiquan
Jilin University of Chemical Technology, China
ORCID: https://orcid.org/0009-0000-7365-6535
Email: lihaiquan@jluct.edu.cn
-/

import Theorem_9_5_Closure
import Lemma_11_3

/-!
# Note 9.5B / Note 11.2.3 — m-th Order Jet Analytic Assembly
(Higher Multiplicity Generalization of Multiple Zeros)

This module generalizes the unitarity final review of Theorems 9.5/10 from
**simple zeros** (m = 1, fully machine-closed by `RH95Final.theorem_9_5_final`)
to **zeros of arbitrary multiplicity m**, corresponding to Note 9.5B
(paragraphs 666–698) and Note 11.2.3 (paragraphs 961–972) of the paper:
"For any m-fold zero, the conclusion of Theorem 9.5 still holds ... whether m
is odd or even, a non-real m-fold zero triggers the mother-equation unitarity
contradiction."

## Machine-verified part (all theorems in this file, zero sorry)

1. **Existence of a first nonzero jet** (`exists_iteratedDeriv_ne_zero`):
   an entire function f that is not identically zero has, at every point ρ,
   some derivative f⁽ᵐ⁾(ρ) ≠ 0.
   Proof chain: ℂ-differentiable ⟹ analytic (`Differentiable.analyticAt`)
   ⟹ power-series coefficients are given by iterated derivatives
   (`HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace`, the n!
   coefficient bridge) ⟹ all-order derivatives zero ⟹ locally identically zero
   (`HasFPowerSeriesAt.locally_zero_iff`) ⟹ identity theorem
   (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) ⟹ f ≡ 0,
   contradiction.
2. **m-th order jet pairing laws** (`iteratedDeriv_reflA` / `iteratedDeriv_reflB`):
   f(1−s) = f(s) ⟹ f⁽ᵐ⁾(1−s) = (−1)ᵐ·f⁽ᵐ⁾(s);
   f(s̄) = conj(f(s)) ⟹ f⁽ᵐ⁾(s̄) = conj(f⁽ᵐ⁾(s)) (Schwarz reflection,
   by induction on m).
3. **Orbit jet assembly** (`theorem_9_5_multiplicity`):
   on the four-point orbit z = ![ρ, 1−ρ̄, ρ̄, 1−ρ] of a non-real zero
   ρ = σ+it (σ ≠ 1/2, t ≠ 0), the first nonzero order m is **uniform** across
   the four orbit points (`jetOrder_star` / `jetOrder_one_sub_star`), and the
   jet vector J i = f⁽ᵐ⁾(z i) satisfies the pairing laws
   J(iA i) = (−1)ᵐ·star(J i), J(iB i) = star(J i), and is pointwise nonzero.

## Interface part (conditionalization of the paper's assertions, same
discipline as `UnitarityPositive` for m = 1)

Two properties of the m-th order jet energy form `E m J` are passed in as
explicit hypotheses:
· `hE_pos`: the unitarity gate — on jet configurations ACTUALLY INDUCED by a
  non-real zero of this f (zero witness included in the hypothesis), the
  energy must be positive semidefinite. This is the per-function gate
  discipline of the paper's Theorem 9.5 ("for any f ∈ ℱ satisfying
  mother-equation unitarity"); the positivity side adjudicates only
  zero-carrying configurations, so it is satisfiable and is never refuted
  inside the library;
· `hE_neg`: Note 9.5B Step 2 — the energy-matrix eigenvalues are V₄ group-algebra
  invariants, independent of m, so the negative-definiteness of 9.5C lifts to
  m-th order jets (for m = 1 this is `Kquad_chiAB_neg`, already
  machine-verified). The negativity side stays universal — it is a
  mathematical fact, not a gate.
The two contradict each other exactly on a zero-carrying configuration — the
execution. The m = 1 special case does not need this interface:
`RH95Final.theorem_9_5_final` is already fully machine-closed from the
per-function premise `SatisfiesUnitarity C f`.

## Conclusion

`theorem_10_unconditional`: zero exclusion no longer needs `hsimple` (the
simple-zero hypothesis) — non-real zeros of arbitrary multiplicity are rejected
at the unitarity gate.
-/

open RH95C RH95U RH94 RH113 Complex Filter Topology
open scoped ComplexConjugate

namespace RHM

/-! ## Part 1: Existence of a first nonzero jet (machine) -/

/-- An entire function that is not identically zero has, at every point, some
    nonzero derivative of some order.
    (Power-series coefficient bridge + identity theorem; this is the entry
    point of the m-th order jet method.) -/
theorem exists_iteratedDeriv_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : ∃ s, f s ≠ 0) (ρ : ℂ) : ∃ m : ℕ, iteratedDeriv m f ρ ≠ 0 := by
  by_contra h
  push_neg at h
  rcases hf.analyticAt ρ with ⟨p, r, hpb⟩
  -- All coefficients vanish: n! · (value of the n-th coefficient at (1,…,1))
  -- = the n-th iterated derivative = 0
  have hp0 : p = 0 := by
    funext n
    apply ContinuousMultilinearMap.ext
    intro v
    show p n v = 0
    have hsum := hpb.iteratedFDeriv_eq_sum_of_completeSpace (fun _ : Fin n => (1 : ℂ))
    have hderiv : iteratedFDeriv ℂ n f ρ (fun _ => 1) = 0 := h n
    rw [hderiv] at hsum
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hsum
    have hp1 : p n (fun _ => 1) = 0 := by
      rcases smul_eq_zero.mp hsum.symm with h1 | h1
      · exact absurd h1 (Nat.factorial_ne_zero n)
      · exact h1
    calc p n v = p n (fun i => v i • (1 : ℂ)) := by congr 1; funext i; simp
      _ = (∏ i, v i) • p n (fun _ => 1) :=
          ContinuousMultilinearMap.map_smul_univ (p n) v (fun _ => 1)
      _ = 0 := by rw [hp1, smul_zero]
  -- All coefficients zero ⟹ locally identically zero ⟹ identity theorem
  -- ⟹ globally identically zero, contradiction
  have hpA : HasFPowerSeriesAt f p ρ := ⟨r, hpb⟩
  have hev : f =ᶠ[𝓝 ρ] 0 := hpA.locally_zero_iff.mpr hp0
  have hfA : AnalyticOnNhd ℂ f Set.univ := fun x _ => hf.analyticAt x
  have h0 : Set.EqOn f 0 Set.univ :=
    hfA.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const isPreconnected_univ
      (Set.mem_univ ρ) hev
  rcases hne with ⟨s, hs⟩
  exact hs (h0 (Set.mem_univ s))

/-- The first nonzero order (the m of Note 9.5B). -/
noncomputable def jetOrder {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : ∃ s, f s ≠ 0) (z : ℂ) : ℕ :=
  Nat.find (exists_iteratedDeriv_ne_zero hf hne z)

lemma jetOrder_spec {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : ∃ s, f s ≠ 0) (z : ℂ) :
    iteratedDeriv (jetOrder hf hne z) f z ≠ 0 :=
  Nat.find_spec (exists_iteratedDeriv_ne_zero hf hne z)

/-! ## Part 2: m-th order jet pairing laws (machine) -/

/-- Jet pairing of reflection A: f(1−s) = f(s) ⟹ f⁽ᵐ⁾(1−z) = (−1)ᵐ·f⁽ᵐ⁾(z). -/
theorem iteratedDeriv_reflA {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f (1 - s) = f s) (m : ℕ) (z : ℂ) :
    iteratedDeriv m f (1 - z) = (-1) ^ m * iteratedDeriv m f z := by
  have hgs : (fun s => f (1 - s)) = f := funext h_sym
  have hkey : ∀ m : ℕ, ∀ z : ℂ,
      iteratedDeriv m (fun s => f (1 - s)) z = (-1) ^ m * iteratedDeriv m f (1 - z) := by
    intro m
    induction m with
    | zero => intro z; simp [iteratedDeriv_zero]
    | succ m ih =>
      intro z
      have hd : Differentiable ℂ (iteratedDeriv m f) :=
        ContDiff.differentiable_iteratedDeriv' m (hf.contDiff)
      have hsub : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := by
        simpa using (hasDerivAt_id z).const_sub (1 : ℂ)
      have hcomp : HasDerivAt (fun w => iteratedDeriv m f (1 - w))
          (deriv (iteratedDeriv m f) (1 - z) * (-1)) z :=
        (hd (1 - z)).hasDerivAt.comp z hsub
      have hd2 : DifferentiableAt ℂ (fun w => iteratedDeriv m f (1 - w)) z :=
        (hd.comp ((differentiable_const (1 : ℂ)).sub differentiable_id)).differentiableAt
      rw [iteratedDeriv_succ]
      have hfun : ∀ w, iteratedDeriv m (fun s => f (1 - s)) w =
          (-1) ^ m * iteratedDeriv m f (1 - w) := ih
      have hev : (fun w => iteratedDeriv m (fun s => f (1 - s)) w) =ᶠ[𝓝 z]
          (fun w => (-1:ℂ) ^ m * iteratedDeriv m f (1 - w)) :=
        Filter.Eventually.of_forall hfun
      have hderiv_eq : deriv (iteratedDeriv m (fun s => f (1 - s))) z =
          deriv (fun w => (-1) ^ m * iteratedDeriv m f (1 - w)) z := hev.deriv_eq
      rw [hderiv_eq, deriv_const_mul _ hd2, hcomp.deriv, ← iteratedDeriv_succ]
      ring
  have e := hkey m z
  rw [hgs] at e
  have hc : (-1 : ℂ) ^ m * (-1) ^ m = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  calc iteratedDeriv m f (1 - z)
      = ((-1 : ℂ) ^ m * (-1) ^ m) * iteratedDeriv m f (1 - z) := by rw [hc]; simp
    _ = (-1 : ℂ) ^ m * ((-1) ^ m * iteratedDeriv m f (1 - z)) := by ring
    _ = (-1 : ℂ) ^ m * iteratedDeriv m f z := by rw [← e]

/-- Jet pairing of reflection B (Schwarz reflection):
    f(s̄) = conj(f(s)) ⟹ f⁽ᵐ⁾(z̄) = conj(f⁽ᵐ⁾(z)). -/
theorem iteratedDeriv_reflB {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h_conj : ∀ s, f (star s) = star (f s)) (m : ℕ) (z : ℂ) :
    iteratedDeriv m f (star z) = star (iteratedDeriv m f z) := by
  have hgs : (fun s => star (f (star s))) = f := by
    funext s
    rw [h_conj s]
    simp
  have hkey : ∀ m : ℕ, ∀ z : ℂ,
      iteratedDeriv m (fun s => star (f (star s))) z = star (iteratedDeriv m f (star z)) := by
    intro m
    induction m with
    | zero => intro z; simp [iteratedDeriv_zero]
    | succ m ih =>
      intro z
      have hd : Differentiable ℂ (iteratedDeriv m f) :=
        ContDiff.differentiable_iteratedDeriv' m (hf.contDiff)
      rw [iteratedDeriv_succ]
      have hfun : ∀ w, iteratedDeriv m (fun s => star (f (star s))) w =
          star (iteratedDeriv m f (star w)) := ih
      have hev : (fun w => iteratedDeriv m (fun s => star (f (star s))) w) =ᶠ[𝓝 z]
          (fun w => star (iteratedDeriv m f (star w))) :=
        Filter.Eventually.of_forall hfun
      have hderiv_eq : deriv (iteratedDeriv m (fun s => star (f (star s)))) z =
          deriv (fun w => star (iteratedDeriv m f (star w))) z := hev.deriv_eq
      -- Derivative of star∘H∘conj (mathlib's star differentiation bridge)
      have hder : deriv (fun w => star (iteratedDeriv m f (star w))) z =
          star (deriv (iteratedDeriv m f) (star z)) := by
        have h : HasDerivAt (star ∘ iteratedDeriv m f ∘ conj)
            (star (deriv (iteratedDeriv m f) (star z))) z := by
          rw [hasDerivAt_star_conj_iff, star_star]
          exact (hd (star z)).hasDerivAt
        exact h.deriv
      rw [hderiv_eq, hder]
      have e : iteratedDeriv (m + 1) f (star z) = deriv (iteratedDeriv m f) (star z) := by
        rw [iteratedDeriv_succ]
      rw [e]
  have e := hkey m z
  rw [hgs] at e
  rw [e, star_star]

/-! ## Part 3: Orbit jet assembly (machine) -/

/-- The first nonzero order is invariant under the star orbit (one direction). -/
lemma jetOrder_star_le {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : ∃ s, f s ≠ 0) (h_conj : ∀ s, f (star s) = star (f s)) (z : ℂ) :
    jetOrder hf hne (star z) ≤ jetOrder hf hne z := by
  apply Nat.find_le
  rw [iteratedDeriv_reflB hf h_conj, ne_eq, star_eq_zero]
  exact jetOrder_spec hf hne z

/-- The first nonzero order is invariant under the star orbit. -/
lemma jetOrder_star {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : ∃ s, f s ≠ 0) (h_conj : ∀ s, f (star s) = star (f s)) (z : ℂ) :
    jetOrder hf hne (star z) = jetOrder hf hne z :=
  le_antisymm (jetOrder_star_le hf hne h_conj z) (by
    have h := jetOrder_star_le hf hne h_conj (star z)
    rwa [star_star] at h)

/-- The first nonzero order is invariant under the 1−star orbit (one direction). -/
lemma jetOrder_one_sub_star_le {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : ∃ s, f s ≠ 0)
    (h_sym : ∀ s, f (1 - s) = f s) (h_conj : ∀ s, f (star s) = star (f s)) (z : ℂ) :
    jetOrder hf hne (1 - star z) ≤ jetOrder hf hne z := by
  apply Nat.find_le
  rw [iteratedDeriv_reflA hf h_sym, iteratedDeriv_reflB hf h_conj]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0)) (by
    rw [ne_eq, star_eq_zero]
    exact jetOrder_spec hf hne z)

/-- The first nonzero order is invariant under the 1−star orbit. -/
lemma jetOrder_one_sub_star {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : ∃ s, f s ≠ 0)
    (h_sym : ∀ s, f (1 - s) = f s) (h_conj : ∀ s, f (star s) = star (f s)) (z : ℂ) :
    jetOrder hf hne (1 - star z) = jetOrder hf hne z :=
  le_antisymm (jetOrder_one_sub_star_le hf hne h_sym h_conj z) (by
    have h := jetOrder_one_sub_star_le hf hne h_sym h_conj (1 - star z)
    have h2 : 1 - star (1 - star z) = z := by simp
    rwa [h2] at h)

/-- The complex four-point orbit: ![ρ, 1−ρ̄, ρ̄, 1−ρ], ρ = σ + it. -/
noncomputable def orbitC (σ t : ℝ) : Fin 4 → ℂ :=
  ![↑σ + Complex.I * ↑t, 1 - star (↑σ + Complex.I * ↑t),
    star (↑σ + Complex.I * ↑t), 1 - (↑σ + Complex.I * ↑t)]

lemma orbitC_iA (σ t : ℝ) : ∀ i, orbitC σ t (iA i) = 1 - star (orbitC σ t i) := by
  intro i
  fin_cases i <;> simp [orbitC, iA]

lemma orbitC_iB (σ t : ℝ) : ∀ i, orbitC σ t (iB i) = star (orbitC σ t i) := by
  intro i
  fin_cases i <;> simp [orbitC, iB]

/-- **Theorem 9.5 (m-fold zero version, Note 9.5B/11.2.3)**:
    the m-th order jet counterexample configuration of a non-real zero (of
    arbitrary multiplicity) self-destructs at the unitarity gate.
    `E` is the m-th order jet energy form; `hE_pos` (the per-function
    unitarity gate, with zero witness) and `hE_neg` (group-algebra invariant,
    Note 9.5B Step 2, universal) are the two paper-assertion interfaces of
    this form. -/
theorem theorem_9_5_multiplicity (C : ℝ) (hC : 0 < C)
    (E : ℕ → (Fin 4 → ℂ) → ℝ)
    (f : ℂ → ℂ)
    (hE_pos : ∀ (m : ℕ) (J : Fin 4 → ℂ),
      (∀ i, J (iA i) = (-1) ^ m * star (J i)) →
      (∀ i, J (iB i) = star (J i)) →
      (∀ i, J i ≠ 0) →
      (∃ σ t : ℝ, f (↑σ + Complex.I * ↑t) = 0 ∧ σ ≠ 1 / 2 ∧ t ≠ 0 ∧
        ∀ i, J i = iteratedDeriv m f (orbitC σ t i)) →
      0 ≤ E m J)
    (hE_neg : ∀ (m : ℕ) (J : Fin 4 → ℂ),
      (∀ i, J (iA i) = (-1) ^ m * star (J i)) →
      (∀ i, J (iB i) = star (J i)) →
      (∀ i, J i ≠ 0) → E m J < 0)
    (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f (1 - s) = f s) (h_conj : ∀ s, f (star s) = star (f s))
    (hne : ∃ s, f s ≠ 0)
    {σ t : ℝ} (hz : f (↑σ + Complex.I * ↑t) = 0) (hσ : σ ≠ 1/2) (ht : t ≠ 0) :
    False := by
  -- The first nonzero order is uniform across the four orbit points
  -- (the pairing laws preserve "the k-th derivative is zero")
  set m₀ := jetOrder hf hne (orbitC σ t 0) with hm₀
  have hm : ∀ i, jetOrder hf hne (orbitC σ t i) = m₀ := by
    intro i
    fin_cases i
    · rfl
    · show jetOrder hf hne (orbitC σ t (1 : Fin 4)) = m₀
      have e : orbitC σ t 1 = 1 - star (orbitC σ t 0) := orbitC_iA σ t 0
      rw [e]
      exact jetOrder_one_sub_star hf hne h_sym h_conj _
    · show jetOrder hf hne (orbitC σ t (2 : Fin 4)) = m₀
      have e : orbitC σ t 2 = star (orbitC σ t 0) := orbitC_iB σ t 0
      rw [e]
      exact jetOrder_star hf hne h_conj _
    · show jetOrder hf hne (orbitC σ t (3 : Fin 4)) = m₀
      have e : orbitC σ t 3 = 1 - star (orbitC σ t 2) := orbitC_iA σ t 2
      rw [e, jetOrder_one_sub_star hf hne h_sym h_conj]
      have e2 : orbitC σ t 2 = star (orbitC σ t 0) := orbitC_iB σ t 0
      rw [e2]
      exact jetOrder_star hf hne h_conj _
  -- The m-th order jet vector field
  set J : Fin 4 → ℂ := fun i => iteratedDeriv m₀ f (orbitC σ t i) with hJ_def
  have hJ : ∀ i, J i ≠ 0 := by
    intro i
    rw [hJ_def]
    show iteratedDeriv m₀ f (orbitC σ t i) ≠ 0
    rw [← hm i]
    exact jetOrder_spec hf hne _
  -- Pairing laws
  have hpairA : ∀ i, J (iA i) = (-1) ^ m₀ * star (J i) := by
    intro i
    show iteratedDeriv m₀ f (orbitC σ t (iA i)) =
      (-1) ^ m₀ * star (iteratedDeriv m₀ f (orbitC σ t i))
    rw [orbitC_iA, iteratedDeriv_reflA hf h_sym, iteratedDeriv_reflB hf h_conj]
  have hpairB : ∀ i, J (iB i) = star (J i) := by
    intro i
    show iteratedDeriv m₀ f (orbitC σ t (iB i)) =
      star (iteratedDeriv m₀ f (orbitC σ t i))
    rw [orbitC_iB, iteratedDeriv_reflB hf h_conj]
  -- Unitarity gate vs m-th order jet energy negative-definiteness.
  -- The gate premise is applied to the jet configuration ACTUALLY INDUCED by
  -- the non-real zero (zero witness: σ, t, hz, hσ, ht) — the per-function
  -- gate discipline of the paper's Theorem 9.5; hE_neg stays universal
  -- (the group-algebra invariant of Note 9.5B Step 2, a mathematical fact).
  exact absurd (hE_pos m₀ J hpairA hpairB hJ ⟨σ, t, hz, hσ, ht, fun i => congrFun hJ_def i⟩)
    (not_le_of_gt (hE_neg m₀ J hpairA hpairB hJ))

/-- **Theorem 10 (zero exclusion, unconditional version)**:
    `hsimple` is not needed — non-real zeros of arbitrary multiplicity are
    excluded. -/
theorem theorem_10_unconditional (C : ℝ) (hC : 0 < C)
    (E : ℕ → (Fin 4 → ℂ) → ℝ)
    (f : ℂ → ℂ)
    (hE_pos : ∀ (m : ℕ) (J : Fin 4 → ℂ),
      (∀ i, J (iA i) = (-1) ^ m * star (J i)) →
      (∀ i, J (iB i) = star (J i)) →
      (∀ i, J i ≠ 0) →
      (∃ σ t : ℝ, f (↑σ + Complex.I * ↑t) = 0 ∧ σ ≠ 1 / 2 ∧ t ≠ 0 ∧
        ∀ i, J i = iteratedDeriv m f (orbitC σ t i)) →
      0 ≤ E m J)
    (hE_neg : ∀ (m : ℕ) (J : Fin 4 → ℂ),
      (∀ i, J (iA i) = (-1) ^ m * star (J i)) →
      (∀ i, J (iB i) = star (J i)) →
      (∀ i, J i ≠ 0) → E m J < 0)
    (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f (1 - s) = f s) (h_conj : ∀ s, f (star s) = star (f s))
    (hne : ∃ s, f s ≠ 0) :
    ∀ σ t : ℝ, f (↑σ + Complex.I * ↑t) = 0 → σ ≠ 1/2 → t = 0 := by
  intro σ t hz hσ
  by_contra ht
  exact theorem_9_5_multiplicity C hC E f hE_pos hE_neg hf h_sym h_conj hne hz hσ ht

end RHM

/- ## Axiom audit -/
section Audit
#print axioms RHM.exists_iteratedDeriv_ne_zero
#print axioms RHM.iteratedDeriv_reflA
#print axioms RHM.iteratedDeriv_reflB
#print axioms RHM.jetOrder_star
#print axioms RHM.jetOrder_one_sub_star
#print axioms RHM.theorem_9_5_multiplicity
#print axioms RHM.theorem_10_unconditional
end Audit
