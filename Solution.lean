import Mathlib
import Lemma_9_5C
import Unitarity_Assembly
import Lemma_9_4
import Theorem_9_5_Closure
import Lemma_11_3
import Final_Assembly

/-!
# Solution

Proves `RHConditional.riemann_hypothesis_conditional` by the closed conditional
chain `RHFinal.RH_xi`. Challenge and Solution are separate Lake libraries (Palomar
template layout) and do not import each other; the compared declaration and its
supporting definitions are restated here with the same types.
-/

namespace RHConditional

/-- Riemann's xi function, `xi s = (s (s − 1) / 2) · Λ(s)`. -/
noncomputable def xi (s : ℂ) : ℂ := (s * (s - 1) / 2) * completedRiemannZeta s

/-- The field `v = Im f` in real coordinates. -/
def vim (f : ℂ → ℂ) (u : ℝ × ℝ) : ℝ := (f (↑u.1 + ↑u.2 * Complex.I)).im

/-- The real gradient of `v = Im f`. -/
noncomputable def nablaV (f : ℂ → ℂ) (u : ℝ × ℝ) : ℝ × ℝ :=
  (deriv (fun x => vim f (x, u.2)) u.1, deriv (fun y => vim f (u.1, y)) u.2)

/-- The four point orbit of `σ + iγ` under the two reflections. -/
def orbit (σ γ : ℝ) : Fin 4 → ℝ × ℝ :=
  ![(σ, γ), (1 - σ, γ), (σ, -γ), (1 - σ, -γ)]

/-- The orbit gradient field. -/
noncomputable def orbitGrad (f : ℂ → ℂ) (σ γ : ℝ) : Fin 4 → ℝ × ℝ :=
  fun i => nablaV f (orbit σ γ i)

/-- Dot product on ℝ². -/
def dot (w u : ℝ × ℝ) : ℝ := w.1 * u.1 + w.2 * u.2

/-- Jacobian of reflection A, `diag (−1, 1)`. -/
def JA (u : ℝ × ℝ) : ℝ × ℝ := (-u.1, u.2)

/-- Jacobian of reflection B, `diag (1, −1)`. -/
def JB (u : ℝ × ℝ) : ℝ × ℝ := (u.1, -u.2)

/-- Channel A partner indices, `0 ↔ 1`, `2 ↔ 3`. -/
def iA : Fin 4 → Fin 4 := ![1, 0, 3, 2]

/-- Channel B partner indices, `0 ↔ 2`, `1 ↔ 3`. -/
def iB : Fin 4 → Fin 4 := ![2, 3, 0, 1]

/-- The geometric energy quadratic form on the eight dimensional gradient space. -/
noncomputable def Kquad (C : ℝ) (w : Fin 4 → ℝ × ℝ) : ℝ :=
  (C / 4) * ∑ i : Fin 4, (dot (w i) (JA (w (iA i))) + dot (w i) (JB (w (iB i))))

/-- The unitarity gate: at every zero of `f` with `Re ≠ 1/2` and `Im ≠ 0`
    (off-critical-line non-real zeros) the orbit gradient energy is strictly
    positive. -/
def SatisfiesUnitarity (C : ℝ) (f : ℂ → ℂ) : Prop :=
  ∀ σ t : ℝ, f (↑σ + Complex.I * ↑t) = 0 → σ ≠ 1 / 2 → t ≠ 0 →
    0 < Kquad C (orbitGrad f σ t)

/-- Proof of the Challenge statement, discharged by `RHFinal.RH_xi`. -/
theorem riemann_hypothesis_conditional (C : ℝ) (hC : 0 < C)
    (g : ℂ → ℂ)
    (hg : Differentiable ℂ g)
    (hg_sym : ∀ s, g (1 - s) = g s)
    (hg_conj : ∀ s, g (star s) = star (g s))
    (hg_simple : ∀ σ t : ℝ, g (↑σ + Complex.I * ↑t) = 0 →
      deriv g (↑σ + Complex.I * ↑t) ≠ 0)
    (hg_eq : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → g s = xi s)
    (hζ : ∀ x : ℝ, 0 < x → x < 1 → (riemannZeta (x : ℂ)).re < 0)
    (hgate : SatisfiesUnitarity C g) :
    ∀ s : ℂ, s ≠ 0 → s ≠ 1 → xi s = 0 → s.re = 1 / 2 := by
  intro s hs0 hs1 hs
  have hg0 : g s = 0 := by rw [hg_eq s hs0 hs1]; exact hs
  have heq' : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → g s = RH113.xiFn s := fun s h0 h1 =>
    hg_eq s h0 h1
  have hgate' : RH95Final.SatisfiesUnitarity C g := hgate
  exact RHFinal.RH_xi C hC g hg hgate' hζ heq' hg_sym hg_conj hg_simple hg0 hs0 hs1

end RHConditional
