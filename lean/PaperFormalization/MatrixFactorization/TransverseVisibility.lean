import PaperFormalization.MatrixFactorization.GaussianVisibility

/-! # MF09: visibility lower bounds and an actual unit tangent direction

The Jensen bound is proved for the original Gaussian law. Normalizing its
nonzero transverse mean gives a concrete unit tangent direction, with no
positive-signal premise. The identification of this mean with the manuscript's
active weighted teacher moment is a separate Gaussian pairing calculation.
-/
open MeasureTheory ProbabilityTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

theorem probability_integral_sq_ge_sq_integral {α : Type*} [MeasurableSpace α]
    (mu : Measure α) [IsProbabilityMeasure mu] (f : α → Real)
    (hf : Integrable f mu) (hf2 : Integrable (fun z => (f z)^2) mu) :
    (∫ z, f z ∂mu)^2 ≤ ∫ z, (f z)^2 ∂mu := by
  let m := ∫ z, f z ∂mu
  have hn : 0 ≤ ∫ z, (f z-m)^2 ∂mu := integral_nonneg (fun z => sq_nonneg _)
  have he : (fun z => (f z-m)^2) = (fun z => (f z)^2-(2*m)*f z+m^2) := by
    funext z
    ring
  rw [he] at hn
  have hsub := hf2.sub (hf.const_mul (2*m))
  rw [integral_add (f := fun z => (f z)^2-(2*m)*f z) (g := fun _ => m^2)
    hsub (integrable_const _),
    integral_sub (f := fun z => (f z)^2) (g := fun z => (2*m)*f z)
      hf2 (hf.const_mul _), integral_const_mul] at hn
  simp only [integral_const, probReal_univ, one_smul] at hn
  change 0 ≤ (∫ z, (f z)^2 ∂mu)-(2*m)*m+m^2 at hn
  change m^2 ≤ _
  nlinarith

theorem gaussianTransverseVector_pairing_sq_integrable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] (s : Weight d) :
    Integrable (fun z => (inner Real s (gaussianTransverseVector O a pole teacher z))^2)
      (stdGaussian (Weight d)) := by
  have hi := (gaussianTransverseVector_norm_pow_integrable O a pole teacher 2).const_mul (norm s^2)
  have hm : StronglyMeasurable (fun z =>
      (inner Real s (gaussianTransverseVector O a pole teacher z))^2) :=
    (stronglyMeasurable_const.inner (𝕜 := Real)
    (gaussianTransverseVector_stronglyMeasurable O a pole teacher)).pow 2
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hb := pow_le_pow_left₀ (abs_nonneg _)
    (abs_real_inner_le_norm s (gaussianTransverseVector O a pole teacher z)) 2
  simpa only [sq_abs, mul_pow] using hb

/-- This representation uses the original teacher feature and Gaussian law. -/
theorem transverseTeacherSignal_eq_gaussian_vector {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    (s : Weight d) (hs : inner Real pole.val s = 0) :
    transverseTeacherSignal O a pole s teacher =
      ∫ z, (inner Real s (gaussianTransverseVector O a pole teacher z))^2
        ∂stdGaussian (Weight d) := by
  unfold transverseTeacherSignal
  apply integral_congr_ae
  filter_upwards with z
  rw [gaussianTransverseVector_pairing O a pole teacher s z hs]

theorem transverseTeacherSignal_ge_mean_pairing_sq {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] (s : Weight d) (hs : inner Real pole.val s = 0) :
    (inner Real s (gaussianTransverseMean O a pole teacher))^2 ≤
      transverseTeacherSignal O a pole s teacher := by
  rw [transverseTeacherSignal_eq_gaussian_vector O a pole teacher s hs]
  have hi := gaussianTransverseVector_integrable O a pole teacher
  have hj := probability_integral_sq_ge_sq_integral (stdGaussian (Weight d))
    (fun z => inner Real s (gaussianTransverseVector O a pole teacher z))
    (hi.const_inner s) (gaussianTransverseVector_pairing_sq_integrable O a pole teacher s)
  rwa [integral_inner hi s] at hj

noncomputable def gaussianVisibilityDirection {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d)) : Weight d :=
  (norm (gaussianTransverseMean O a pole teacher))⁻¹ • gaussianTransverseMean O a pole teacher

theorem gaussianVisibilityDirection_tangent {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] :
    inner Real pole.val (gaussianVisibilityDirection O a pole teacher) = 0 := by
  simp only [gaussianVisibilityDirection, real_inner_smul_right,
    gaussianTransverseMean_tangent, mul_zero]

theorem gaussianVisibilityDirection_norm {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    (hmean : gaussianTransverseMean O a pole teacher ≠ 0) :
    norm (gaussianVisibilityDirection O a pole teacher) = 1 := by
  rw [gaussianVisibilityDirection, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hmean)]

theorem gaussianVisibilityDirection_pairing {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    (hmean : gaussianTransverseMean O a pole teacher ≠ 0) :
    inner Real (gaussianVisibilityDirection O a pole teacher)
      (gaussianTransverseMean O a pole teacher) = norm (gaussianTransverseMean O a pole teacher) := by
  rw [gaussianVisibilityDirection, real_inner_smul_left, real_inner_self_eq_norm_sq]
  field_simp

theorem gaussianVisibilityDirection_signal_lower {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] (hmean : gaussianTransverseMean O a pole teacher ≠ 0) :
    norm (gaussianTransverseMean O a pole teacher)^2 ≤
      transverseTeacherSignal O a pole (gaussianVisibilityDirection O a pole teacher) teacher := by
  have hj := transverseTeacherSignal_ge_mean_pairing_sq O a pole teacher
    (gaussianVisibilityDirection O a pole teacher) (gaussianVisibilityDirection_tangent O a pole teacher)
  rwa [gaussianVisibilityDirection_pairing O a pole teacher hmean] at hj

/-- A nonzero actual Gaussian mean produces a visible unit direction. The
nonvanishing input is intended to be discharged by the weighted-moment theorem. -/
theorem exists_unit_transverse_positive_signal_of_mean_ne_zero {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] (hmean : gaussianTransverseMean O a pole teacher ≠ 0) :
    ∃ s : Weight d, inner Real pole.val s = 0 ∧ norm s = 1 ∧
      norm (gaussianTransverseMean O a pole teacher)^2 ≤ transverseTeacherSignal O a pole s teacher ∧
      0 < transverseTeacherSignal O a pole s teacher := by
  have hlo := gaussianVisibilityDirection_signal_lower O a pole teacher hmean
  exact ⟨gaussianVisibilityDirection O a pole teacher,
    gaussianVisibilityDirection_tangent O a pole teacher,
    gaussianVisibilityDirection_norm O a pole teacher hmean, hlo,
    lt_of_lt_of_le (sq_pos_of_pos (norm_pos_iff.mpr hmean)) hlo⟩

end PaperFormalization.MatrixFactorization
