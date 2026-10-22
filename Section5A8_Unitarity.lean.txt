import Mathlib.Analysis.SpecialFunctions.Exp

/-!
5A.8 only.

`SpectralReading.hSpec` is the explicit premise that the spectrum of the diagonal
operator is the zero set `Z`. This file proves that, under that premise, the five
statements of 5A.8 are equivalent. It does not prove that the roots are real.
-/

open Complex Real Filter

namespace Section5A8

/-- Explicit spectral reading. `hSpec` packages premise P1: `Spec L = Z`. -/
structure SpectralReading (ι : Type*) where
  α : ι → ℂ
  Z : Set ℂ
  hSpec : Set.range α = Z

/-- Diagonal action on one coefficient: `L e_i = α_i e_i`. -/
def applyL {ι : Type*} (R : SpectralReading ι) (i : ι) (c : ℂ) : ℂ :=
  R.α i * c

/-- Evolution on one eigen-direction: `U(τ) e_i = exp(i τ α_i) e_i`. -/
noncomputable def applyU {ι : Type*} (R : SpectralReading ι) (τ : ℝ) (i : ι) (c : ℂ) : ℂ :=
  exp (I * (τ : ℂ) * R.α i) * c

/-- Energy of a basis vector: `⟨e_i, L e_i⟩ = α_i`. -/
def energyBasis {ι : Type*} (R : SpectralReading ι) (i : ι) : ℂ :=
  star (1 : ℂ) * applyL R i 1

def rootsReal {ι : Type*} (R : SpectralReading ι) : Prop :=
  R.Z ⊆ {z : ℂ | z.im = 0}

def specReal {ι : Type*} (R : SpectralReading ι) : Prop :=
  Set.range R.α ⊆ {z : ℂ | z.im = 0}

/-- `L` is symmetric on every eigen-direction. -/
def selfAdjointDiag {ι : Type*} (R : SpectralReading ι) : Prop :=
  ∀ i : ι, ∀ x y : ℂ, star (applyL R i x) * y = star x * applyL R i y

/-- Each eigen-direction evolves by a strongly continuous phase of modulus one. -/
def unitaryGroup {ι : Type*} (R : SpectralReading ι) : Prop :=
  (∀ i : ι, ∀ τ : ℝ, ‖applyU R τ i 1‖ = 1) ∧
    ∀ i : ι, Tendsto (fun τ : ℝ => applyU R τ i 1) (nhds 0) (nhds 1)

/-- The energy of every basis vector is real. -/
def energyReal {ι : Type*} (R : SpectralReading ι) : Prop :=
  ∀ i : ι, (energyBasis R i).im = 0

lemma re_I_mul_ofReal_mul (τ : ℝ) (α : ℂ) : (I * (τ : ℂ) * α).re = -τ * α.im := by
  have hcomm : I * (τ : ℂ) * α = ((τ : ℂ) * α) * I := by
    calc
      I * (τ : ℂ) * α = (τ : ℂ) * I * α := by rw [mul_comm I]
      _ = (τ : ℂ) * (I * α) := by rw [mul_assoc]
      _ = (τ : ℂ) * (α * I) := by rw [mul_comm I α]
      _ = ((τ : ℂ) * α) * I := by rw [mul_assoc]
  rw [hcomm, mul_I_re, mul_im, ofReal_re, ofReal_im]
  ring

lemma star_eq_self_iff_im (α : ℂ) : star α = α ↔ α.im = 0 := by
  constructor
  · intro h
    have him : (star α).im = α.im := congrArg im h
    have : -α.im = α.im := by simpa [star_def, conj_im] using him
    linarith
  · intro h
    refine Complex.ext ?_ ?_
    · simp
    · simp [conj_im, h]

theorem selfAdjoint_iff_real {ι : Type*} (R : SpectralReading ι) :
    selfAdjointDiag R ↔ ∀ i, (R.α i).im = 0 := by
  constructor
  · intro h i
    have h1 : star (R.α i) = R.α i := by simpa [applyL] using h i 1 1
    exact (star_eq_self_iff_im (R.α i)).1 h1
  · intro h i x y
    have hstar : star (R.α i) = R.α i := (star_eq_self_iff_im (R.α i)).2 (h i)
    simp only [applyL]
    rw [star_mul, hstar, mul_assoc]

theorem unitary_iff_real {ι : Type*} (R : SpectralReading ι) :
    (∀ i : ι, ∀ τ : ℝ, ‖applyU R τ i 1‖ = 1) ↔ ∀ i, (R.α i).im = 0 := by
  constructor
  · intro h i
    have hnorm := h i 1
    rw [applyU, Complex.norm_mul, norm_one, mul_one, norm_exp, re_I_mul_ofReal_mul] at hnorm
    rw [Real.exp_eq_one_iff] at hnorm
    simpa using hnorm
  · intro h i τ
    rw [applyU, Complex.norm_mul, norm_one, mul_one, norm_exp, re_I_mul_ofReal_mul, h i]
    simp

/-- The phase is continuous at `τ = 0` on every eigen-direction. -/
theorem mode_strongly_continuous {ι : Type*} (R : SpectralReading ι) (i : ι) :
    Tendsto (fun τ : ℝ => applyU R τ i 1) (nhds 0) (nhds 1) := by
  have hc : Continuous fun τ : ℝ => I * (τ : ℂ) * R.α i :=
    (continuous_ofReal.const_mul I).mul_const (R.α i)
  have htend := (Complex.continuous_exp.comp hc).tendsto (0 : ℝ)
  simp only [applyU, mul_one]
  have h0 : (Complex.exp ∘ fun τ : ℝ => I * (τ : ℂ) * R.α i) 0 = 1 := by
    simp [Complex.exp_zero]
  rw [show (fun τ : ℝ => Complex.exp (I * (τ : ℂ) * R.α i))
      = Complex.exp ∘ fun τ : ℝ => I * (τ : ℂ) * R.α i from rfl]
  rw [← h0]
  exact htend

theorem energy_iff_real {ι : Type*} (R : SpectralReading ι) :
    energyReal R ↔ ∀ i, (R.α i).im = 0 := by
  constructor
  · intro h i
    simpa [energyBasis, applyL] using h i
  · intro h i
    simpa [energyBasis, applyL] using h i

theorem spec_iff_real {ι : Type*} (R : SpectralReading ι) :
    specReal R ↔ ∀ i, (R.α i).im = 0 := by
  constructor
  · intro h i
    exact h ⟨i, rfl⟩
  · intro h z hz
    rcases hz with ⟨i, rfl⟩
    exact h i

theorem roots_iff_spec {ι : Type*} (R : SpectralReading ι) :
    rootsReal R ↔ specReal R := by
  simp [rootsReal, specReal, R.hSpec]

/-- The two terms in `d/dτ ⟨U(τ)x, L U(τ)x⟩` cancel: `-i ‖Lx‖² + i ‖Lx‖² = 0`. -/
theorem energy_derivative_cancels (v : ℂ) :
    star (I * v) * v + star v * (I * v) = 0 := by
  have hI : star I = -I := by rw [star_def, conj_I]
  rw [star_mul, hI, mul_assoc, ← mul_add]
  simp

/-- 5A.8. Under `hSpec : Spec L = Z`, the five statements are equivalent.
This does not prove `rootsReal`. -/
theorem five_eight_equiv {ι : Type*} (R : SpectralReading ι) :
    rootsReal R ↔
      specReal R ∧ selfAdjointDiag R ∧ unitaryGroup R ∧ energyReal R := by
  constructor
  · intro h
    have hmode : ∀ i, (R.α i).im = 0 := (spec_iff_real R).1 ((roots_iff_spec R).1 h)
    refine ⟨(roots_iff_spec R).1 h, (selfAdjoint_iff_real R).2 hmode, ?_, (energy_iff_real R).2 hmode⟩
    exact ⟨(unitary_iff_real R).2 hmode, fun i => mode_strongly_continuous R i⟩
  · rintro ⟨hspec, _, _, _⟩
    exact (roots_iff_spec R).2 hspec

end Section5A8

#print axioms Section5A8.five_eight_equiv
#print axioms Section5A8.selfAdjoint_iff_real
#print axioms Section5A8.unitary_iff_real
#print axioms Section5A8.energy_iff_real
#print axioms Section5A8.spec_iff_real
#print axioms Section5A8.roots_iff_spec
#print axioms Section5A8.mode_strongly_continuous
#print axioms Section5A8.energy_derivative_cancels
