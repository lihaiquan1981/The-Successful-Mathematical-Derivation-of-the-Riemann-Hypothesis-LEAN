import Mathlib
import Theorem_9_3A

/-!
# Solution

Proves `RHStructural.structural_reduction_9_3A` (Theorem 9.3A, structural
dimension reduction for doubly reflected entire functions) by the standalone
machine-verified development `RH93.theorem_9_3A`. Challenge and Solution are
separate Lake libraries (Palomar template layout); the compared declaration
is restated here with the same signature.
-/

namespace RHStructural

/-- **Theorem 9.3A** (structural dimension reduction for doubly reflected
    entire functions). Let f be an entire function satisfying the
    double-reflection symmetry f(s) = f(1 − s) and f(conj s) = conj (f s).
    Then f admits a unique representation f(s) = g((s − 1/2)²) with g entire
    and real-valued on the real axis. Unconditional: no unitarity gate and
    no classical input. -/
theorem structural_reduction_9_3A {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f s = f (1 - s))
    (h_conj : ∀ s, f (star s) = star (f s)) :
    (∃ g : ℂ → ℂ, Differentiable ℂ g ∧ (∀ t : ℝ, (g ↑t).im = 0) ∧
      (∀ s : ℂ, f s = g ((s - 1/2)^2))) ∧
    (∀ g1 g2 : ℂ → ℂ, (∀ s : ℂ, f s = g1 ((s - 1/2)^2)) →
      (∀ s : ℂ, f s = g2 ((s - 1/2)^2)) → g1 = g2) :=
  RH93.theorem_9_3A hf h_sym h_conj

end RHStructural
