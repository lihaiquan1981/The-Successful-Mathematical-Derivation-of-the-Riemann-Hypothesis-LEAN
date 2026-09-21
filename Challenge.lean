import Mathlib

/-!
# Challenge: A machine-checked structural and spectral group for doubly
reflected entire functions and Riemann's xi

This module states a group of eight theorems forming the structural,
analytic and spectral core of the paper "The Successful Mathematical
Derivation of the Forward-Reverse Reversible Bidirectional Closure of the
Riemann Hypothesis" (Li Haiquan), Sections 9.3A, 9.4, 9.5C, 11.3 and the
Mother-Equation core certificate. Six of the eight are fully unconditional;
two carry a single named classical premise (the strict negativity of ζ on
the real interval (0, 1), a standard classical fact stated as an explicit
hypothesis).

The group, in the paper's logical order:

(1) `structural_reduction_9_3A` — factorization through the symmetry
    quotient. Every entire function f satisfying the double-reflection
    symmetry f(s) = f(1 − s) and f(conj s) = conj (f s) admits a unique
    representation f(s) = g((s − 1/2)²) with g entire and real-valued on
    the real axis. Consequently the zero set of f is the preimage under
    the quotient map s ↦ (s − 1/2)² of the zero set of g; in particular,
    zeros of f are organized into orbits of the Klein four-group generated
    by the two reflections s ↦ 1 − s and s ↦ conj s.

(2) `germ_structure_9_4` — reflection structure of the local germ space.
    For v = Im f in real coordinates: v is odd under each of the two
    reflections; v vanishes on the two fixed lines (the critical line
    Re s = 1/2 and the real axis); and at a simple zero of f the real
    gradient ∇v is nonzero (via the Cauchy–Riemann identities).

(3) `real_axis_positivity_11_3` — real-axis positivity of Riemann's xi.
    For real x ∉ {0, 1}, ξ(x) is a strictly positive real number. The
    case x > 1 is machine-proved by termwise positivity of the Dirichlet
    series; x < 0 is covered by the functional equation; 0 < x < 1 uses
    the named classical premise ζ(x) < 0.

(4) `xi_ne_zero_of_quotient_nonneg` — for the ξ-realization, a zero whose
    quotient coordinate w = (s − 1/2)² is a nonnegative real (w ≠ 1/4) is
    excluded (same classical premise).

(5) `critical_line_lock` — if the quotient coordinate w = (s − 1/2)² is a
    negative real, then Re s = 1/2. Unconditional.

(6) `heat_kernel_spectral` (namespace `RHHeat`) — the heat-kernel spectral
    limit of the two-channel orbit energy (Lemma 9.5C), including the
    explicit limit form: (i) the rescaled energy E(α)/α converges (α → 0⁺)
    to the quadratic form K̃ on the eight-dimensional orbit-gradient space;
    (ii) on χAB-type configurations the limit form is given by the
    identity ⟨W, K̃W⟩ = −(C/2)·Σᵢ‖wᵢ‖²; (iii) hence it is strictly
    negative on nonzero χAB-type configurations. Unconditional. The
    FieldData bundle is an abstract data package (bounded measurable
    field, four centers, center gradients, uniform quadratic first-order
    remainder bound around the centers — which in particular forces the
    field to vanish at the four centers); it does not presuppose the
    orbit geometry or C² smoothness. In the repository the bundle is
    instantiated by the four-point reflection orbit and the germ
    gradients of Lemma 9.4.

(7) `two_channel_kernel_spectrum` (namespace `RHMother`) — the complete
    four-mode spectral resolution of the regularized two-channel orbit
    kernel over ℤ (doubled normalization): the eigenvalue list
    {2C+2ε, 2ε, 2ε, −2C+2ε} on the modes {χ0, χA, χB, χAB}, the unitarity
    sign discrimination under the intrinsic boundary C > ε > 0, and the
    phase-transition cliff (minimal eigenvalue jump of exactly 2C between
    collapsed and expanded orbits). Unconditional.

(8) `jet_lift_inheritance` (namespace `RHMother`) — the eight-dimensional
    gradient-jet lift: the simple-zero gradient pattern
    W = (a, b, a, −b, −a, b, −a, −b) inherits the negative eigenvalue
    under the lifted kernel, with the explicit energy identity
    E8 = 4(a²+b²)(−2C+2ε), hence strictly negative energy for a nonzero
    gradient. Unconditional.

Together (3)–(5) state, for real values of the quotient coordinate, the
complete zero-location alternative for ξ: nonnegative ⇒ excluded;
negative ⇒ on the critical line.

The repository additionally contains the paper's full conditional chain
(9.3A → 9.4 → 9.5/9.5C → 11.3 → final assembly), formalized as an explicit
named-premise conditional statement; that chain is an extension of this
artifact, not the registered result.

Layout follows the Palomar template: Challenge depends only on Mathlib; the
compared declarations are the dotted names listed in comparator.json.
-/

namespace RHStructural

/-- **Theorem 9.3A** (factorization of doubly reflected entire functions
    through the symmetry quotient). Let f be an entire function satisfying
    the double-reflection symmetry f(s) = f(1 − s) and
    f(conj s) = conj (f s). Then f admits a unique representation
    f(s) = g((s − 1/2)²) with g entire and real-valued on the real axis.
    Unconditional: no gate and no classical input. -/
theorem structural_reduction_9_3A {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f s = f (1 - s))
    (h_conj : ∀ s, f (star s) = star (f s)) :
    (∃ g : ℂ → ℂ, Differentiable ℂ g ∧ (∀ t : ℝ, (g ↑t).im = 0) ∧
      (∀ s : ℂ, f s = g ((s - 1/2)^2))) ∧
    (∀ g1 g2 : ℂ → ℂ, (∀ s : ℂ, f s = g1 ((s - 1/2)^2)) →
      (∀ s : ℂ, f s = g2 ((s - 1/2)^2)) → g1 = g2) := by
  sorry

/-- **Lemma 9.4** (reflection structure of the local germ space). For
    v = Im f in real coordinates (u = (x, y) standing for s = x + iy):
    (a) v is odd under each reflection, v(1−x, y) = −v(x, y) and
        v(x, −y) = −v(x, y);
    (b) v vanishes on the fixed lines of the two reflections, i.e. on the
        critical line Re s = 1/2 and on the real axis;
    (c) at a simple zero of f (f′ ≠ 0) the real gradient
        ∇v = (∂v/∂x, ∂v/∂y) is nonzero (Cauchy–Riemann).
    Unconditional. -/
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
  sorry

/-- **Lemma 11.3** (real-axis positivity of Riemann's xi). For real
    x ∉ {0, 1}, ξ(x) = (x(x−1)/2)·Λ(x) is a strictly positive real number.
    Named classical premise: ζ(x) < 0 for 0 < x < 1 (a standard classical
    fact about the real interval, stated as an explicit hypothesis; it
    asserts nothing about non-real zeros). -/
theorem real_axis_positivity_11_3
    (hζ : ∀ x : ℝ, 0 < x → x < 1 → (riemannZeta (x : ℂ)).re < 0)
    {x : ℝ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    (0 : ℝ) < (((x : ℂ) * ((x : ℂ) - 1) / 2) * completedRiemannZeta (x : ℂ)).re ∧
    (((x : ℂ) * ((x : ℂ) - 1) / 2) * completedRiemannZeta (x : ℂ)).im = 0 := by
  sorry

/-- **Zero exclusion for nonnegative quotient coordinate** (§11.3 of the
    paper): if w = (s − 1/2)² is a nonnegative real (w ≠ 1/4, the removable
    points s ∈ {0, 1}), then ξ(s) ≠ 0. Same named classical premise. -/
theorem xi_ne_zero_of_quotient_nonneg
    (hζ : ∀ x : ℝ, 0 < x → x < 1 → (riemannZeta (x : ℂ)).re < 0)
    {s : ℂ} {w : ℝ}
    (hw : (s - 1 / 2) ^ 2 = (w : ℂ)) (hw0 : 0 ≤ w) (hwq : w ≠ 1 / 4) :
    (s * (s - 1) / 2) * completedRiemannZeta s ≠ 0 := by
  sorry

/-- **Critical-line lock** (§11.3 of the paper): if the quotient coordinate
    w = (s − 1/2)² is a negative real, then Re s = 1/2, i.e.
    s = 1/2 ± i·√|w| lies on the critical line. Unconditional. -/
theorem critical_line_lock {s : ℂ} {w : ℝ}
    (hw : (s - 1 / 2) ^ 2 = (w : ℂ)) (hwneg : w < 0) :
    s.re = 1 / 2 := by
  sorry

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
    gradients w, and the quadratic Taylor-remainder constant M.
    This is an abstract data package: it does not presuppose that the
    centers form a reflection orbit, nor that Φ is C²; note that the
    remainder bound at u = 0 forces Φ to vanish at the four centers. -/
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

/-- **Lemma 9.5C** (heat-kernel spectral limit for the two-channel orbit
    energy, with the explicit limit form). (i) The rescaled regularized
    energy converges to the K̃ quadratic form; (ii) on chi_AB-type
    configurations the limit form is given by the identity
    ⟨W, K̃ W⟩ = −(C/2)·Σᵢ‖wᵢ‖²; (iii) hence it is strictly negative on
    nonzero chi_AB-type configurations. -/
theorem heat_kernel_spectral (D : FieldData) (hC : 0 < C) :
    (Filter.Tendsto (fun α => Egeom D C α / α) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Kquad C D.w))) ∧
    ((∀ i, D.w (iA i) = JB (D.w i)) → (∀ i, D.w (iB i) = JA (D.w i)) →
      Kquad C D.w = -(C/2) * ∑ i : Fin 4, (nrm2 (D.w i)) ^ 2) ∧
    ((∀ i, D.w (iA i) = JB (D.w i)) → (∀ i, D.w (iB i) = JA (D.w i)) →
      (∃ i : Fin 4, D.w i ≠ 0) → Kquad C D.w < 0) := by
  sorry

end

end RHHeat

namespace RHMother

/-- Integer 4-vectors: fields on the four-point orbit (doubled normalization
    G = 2·Kgeom; all eigenvalues are scaled by the same factor 2, so sign
    conclusions coincide with the original normalization). -/
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

/-- Minimal-eigenvalue function: −2C+2ε on the expanded (non-collapsed)
    orbit, 2ε on the collapsed orbit. -/
def minEig (collapsed : Bool) (C ε : Int) : Int :=
  if collapsed then 2 * ε else -2 * C + 2 * ε

/-- **Two-channel kernel spectrum** (Mother-Equation core certificate,
    Parts III and VI): the complete four-mode spectral resolution of the
    regularized two-channel orbit kernel over ℤ — eigenvalue list
    {2C+2ε, 2ε, 2ε, −2C+2ε} on {χ0, χA, χB, χAB} — together with the
    unitarity sign discrimination under the intrinsic boundary C > ε > 0
    and the phase-transition cliff (jump of exactly 2C, no intermediate
    state). Unconditional. -/
theorem two_channel_kernel_spectrum (C ε : Int) (hC : C > ε) (hε : ε > 0) :
    (rK C ε v0 = smul4 (2 * C + 2 * ε) v0)
    ∧ (rK C ε vA = smul4 (2 * ε) vA)
    ∧ (rK C ε vB = smul4 (2 * ε) vB)
    ∧ (rK C ε vAB = smul4 (-2 * C + 2 * ε) vAB)
    ∧ (-2 * C + 2 * ε < 0 ∧ 2 * C + 2 * ε > 0 ∧ 2 * ε > 0)
    ∧ (minEig false C ε < 0 ∧ minEig true C ε > 0 ∧
        minEig true C ε - minEig false C ε = 2 * C) := by
  sorry

/-- Integer 8-vectors: gradient jets on the four-point orbit. -/
abbrev V8 := Int × Int × Int × Int × Int × Int × Int × Int

/-- Gradient pattern of a simple zero (the χAB-type vector forced by the
    double-reflection symmetry). -/
def W8 (a b : Int) : V8 := (a, b, a, -b, -a, b, -a, -b)

/-- The 8-dimensional doubled-normalization geometric kernel
    G8 = C·(PA⊗JA + PB⊗JB). -/
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

/-- **Jet lift inheritance** (Mother-Equation core certificate, Part V):
    the eight-dimensional gradient jet W = (a, b, a, −b, −a, b, −a, −b) of
    a simple zero inherits the negative eigenvalue under the lifted
    regularized kernel, with the explicit energy identity
    E8 = 4(a²+b²)(−2C+2ε); hence a nonzero gradient induces strictly
    negative energy. Unconditional. -/
theorem jet_lift_inheritance (C ε a b : Int) (hC : C > ε) (hε : ε > 0) :
    (r8 C ε (W8 a b) = smul8 (-2 * C + 2 * ε) (W8 a b))
    ∧ (dot8 (W8 a b) (r8 C ε (W8 a b)) = 4 * (a * a + b * b) * (-2 * C + 2 * ε))
    ∧ ((a ≠ 0 ∨ b ≠ 0) → dot8 (W8 a b) (r8 C ε (W8 a b)) < 0) := by
  sorry

end RHMother
