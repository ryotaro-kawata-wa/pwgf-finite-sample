import PaperFormalization.MatrixFactorization.GaussianVisibilityMatrix

/-! # MF09: the actual covariance operator and its largest eigenvalue

The covariance operator is obtained by integrating the actual rank-one action.
Compactness of the unit sphere supplies a maximum of its Rayleigh quotient;
Mathlib's self-adjoint variational principle identifies that maximum as an
eigenvalue. Positive eigenvectors are tangent because the operator's range is.
-/
open MeasureTheory ProbabilityTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

theorem gaussianVisibilityAction_integrable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] (s : Weight d) :
    Integrable (fun z => inner Real s (gaussianTransverseVector O a pole teacher z) •
      gaussianTransverseVector O a pole teacher z) (stdGaussian (Weight d)) := by
  have hm := gaussianTransverseVector_stronglyMeasurable O a pole teacher
  have hi := (gaussianTransverseVector_norm_pow_integrable O a pole teacher 2).const_mul (norm s)
  apply hi.mono' ((stronglyMeasurable_const.inner (𝕜 := Real) hm).smul hm).aestronglyMeasurable
  filter_upwards with z
  change norm (inner Real s (gaussianTransverseVector O a pole teacher z) •
    gaussianTransverseVector O a pole teacher z) ≤ norm s*norm (gaussianTransverseVector O a pole teacher z)^2
  rw [norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ (norm s*norm (gaussianTransverseVector O a pole teacher z))*
        norm (gaussianTransverseVector O a pole teacher z) :=
      mul_le_mul_of_nonneg_right (abs_real_inner_le_norm _ _) (norm_nonneg _)
    _ = _ := by ring

noncomputable def gaussianVisibilityLinearMap {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] : Weight d →ₗ[Real] Weight d where
  toFun s := ∫ z, inner Real s (gaussianTransverseVector O a pole teacher z) •
    gaussianTransverseVector O a pole teacher z ∂stdGaussian (Weight d)
  map_add' s t := by
    simp only [inner_add_left, add_smul]
    exact integral_add (gaussianVisibilityAction_integrable O a pole teacher s)
      (gaussianVisibilityAction_integrable O a pole teacher t)
  map_smul' c s := by
    simp only [real_inner_smul_left, mul_smul, RingHom.id_apply]
    exact integral_smul c _

noncomputable def gaussianVisibilityOperator {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] : Weight d →L[Real] Weight d :=
  (gaussianVisibilityLinearMap O a pole teacher).toContinuousLinearMap

theorem gaussianVisibilityOperator_apply {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] (s : Weight d) :
    gaussianVisibilityOperator O a pole teacher s =
      ∫ z, inner Real s (gaussianTransverseVector O a pole teacher z) •
        gaussianTransverseVector O a pole teacher z ∂stdGaussian (Weight d) := rfl

theorem gaussianVisibilityOperator_bilinear {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] (s t : Weight d) :
    inner Real t (gaussianVisibilityOperator O a pole teacher s) =
      inner Real (outer s t) (gaussianVisibilityMatrix O a pole teacher) := by
  rw [gaussianVisibilityOperator_apply,
    ← integral_inner (gaussianVisibilityAction_integrable O a pole teacher s),
    gaussianVisibilityMatrix_bilinear]
  simp only [real_inner_smul_right]

theorem gaussianVisibilityOperator_isSelfAdjoint {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] : IsSelfAdjoint (gaussianVisibilityOperator O a pole teacher) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro s t
  change inner Real (gaussianVisibilityOperator O a pole teacher s) t =
    inner Real s (gaussianVisibilityOperator O a pole teacher t)
  rw [real_inner_comm, gaussianVisibilityOperator_bilinear, gaussianVisibilityOperator_bilinear,
    gaussianVisibilityMatrix_bilinear, gaussianVisibilityMatrix_bilinear]
  apply integral_congr_ae
  filter_upwards with z
  ring

theorem gaussianVisibilityOperator_tangent {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] (s : Weight d) :
    inner Real pole.val (gaussianVisibilityOperator O a pole teacher s) = 0 := by
  rw [gaussianVisibilityOperator_apply,
    ← integral_inner (gaussianVisibilityAction_integrable O a pole teacher s)]
  simp only [real_inner_smul_right, gaussianTransverseVector_tangent, mul_zero, integral_zero]

theorem gaussianVisibilityOperator_quadratic {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] (s : Weight d) :
    (gaussianVisibilityOperator O a pole teacher).reApplyInnerSelf s =
      inner Real (outer s s) (gaussianVisibilityMatrix O a pole teacher) := by
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  change inner Real (gaussianVisibilityOperator O a pole teacher s) s = _
  rw [real_inner_comm, gaussianVisibilityOperator_bilinear]

noncomputable def gaussianVisibilityMaxEigenvalue {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] : Real :=
  ⨆ x : {x : Weight d // x ≠ 0},
    (gaussianVisibilityOperator O a pole teacher).rayleighQuotient x

/-- A positive top eigenvalue is attained by a unit tangent vector. The
eigenvalue is the supremum of the actual covariance Rayleigh quotients; its
positivity is proved from the mean, rather than added as a premise. -/
theorem gaussianVisibility_exists_top_eigenvector {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] (hmean : gaussianTransverseMean O a pole teacher ≠ 0) :
    ∃ s : Weight d, norm s = 1 ∧ inner Real pole.val s = 0 ∧
      gaussianVisibilityOperator O a pole teacher s = gaussianVisibilityMaxEigenvalue O a pole teacher • s ∧
      transverseTeacherSignal O a pole s teacher = gaussianVisibilityMaxEigenvalue O a pole teacher ∧
      norm (gaussianTransverseMean O a pole teacher)^2 ≤ gaussianVisibilityMaxEigenvalue O a pole teacher ∧
      0 < gaussianVisibilityMaxEigenvalue O a pole teacher ∧
      ∀ t : Weight d, norm t = 1 →
        inner Real (outer t t) (gaussianVisibilityMatrix O a pole teacher) ≤
          gaussianVisibilityMaxEigenvalue O a pole teacher := by
  let T := gaussianVisibilityOperator O a pole teacher
  let u := gaussianVisibilityDirection O a pole teacher
  have hu : norm u = 1 := gaussianVisibilityDirection_norm O a pole teacher hmean
  have hut : inner Real pole.val u = 0 := gaussianVisibilityDirection_tangent O a pole teacher
  have hmu : u ∈ Metric.sphere (0 : Weight d) 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hu
  obtain ⟨s, hs, hmax⟩ := (isCompact_sphere (0 : Weight d) 1).exists_isMaxOn ⟨u,hmu⟩
    T.reApplyInnerSelf_continuous.continuousOn
  have hsn : norm s = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hs
  have hsz : s ≠ 0 := by intro hz; simpa [hz] using hsn
  have hsq : norm (gaussianTransverseMean O a pole teacher)^2 ≤ T.reApplyInnerSelf s := by
    calc
      _ ≤ transverseTeacherSignal O a pole u teacher :=
        gaussianVisibilityDirection_signal_lower O a pole teacher hmean
      _ = T.reApplyInnerSelf u := by
        rw [gaussianVisibilityOperator_quadratic, gaussianVisibilityMatrix_transverse_signal O a pole teacher u hut]
      _ ≤ _ := hmax hmu
  have hSA : IsSelfAdjoint T := gaussianVisibilityOperator_isSelfAdjoint O a pole teacher
  have hmax' : IsMaxOn T.reApplyInnerSelf (Metric.sphere (0 : Weight d) (norm s)) s := by
    simpa only [hsn] using hmax
  have he := hSA.hasEigenvector_of_isMaxOn hsz hmax'
  have heq : T s = gaussianVisibilityMaxEigenvalue O a pole teacher • s := by
    exact Module.End.mem_eigenspace_iff.mp he.1
  have hvalue : T.reApplyInnerSelf s = gaussianVisibilityMaxEigenvalue O a pole teacher := by
    rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    change inner Real (T s) s = _
    rw [heq, real_inner_smul_left, real_inner_self_eq_norm_sq, hsn]
    ring
  have hlo : norm (gaussianTransverseMean O a pole teacher)^2 ≤
      gaussianVisibilityMaxEigenvalue O a pole teacher := by rwa [hvalue] at hsq
  have hpos : 0 < gaussianVisibilityMaxEigenvalue O a pole teacher :=
    lt_of_lt_of_le (sq_pos_of_pos (norm_pos_iff.mpr hmean)) hlo
  have hst : inner Real pole.val s = 0 := by
    have ht := gaussianVisibilityOperator_tangent O a pole teacher s
    change inner Real pole.val (T s) = 0 at ht
    rw [heq, real_inner_smul_right] at ht
    exact (mul_eq_zero.mp ht).resolve_left (ne_of_gt hpos)
  refine ⟨s, hsn, hst, heq, ?_, hlo, hpos, ?_⟩
  · rw [← gaussianVisibilityMatrix_transverse_signal O a pole teacher s hst,
      ← gaussianVisibilityOperator_quadratic]
    exact hvalue
  · intro t ht
    rw [← gaussianVisibilityOperator_quadratic]
    exact (hmax (by simpa only [Metric.mem_sphere, dist_zero_right] using ht)).trans_eq hvalue

theorem gaussianVisibilityMaxEigenvalue_nonneg {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] : 0 ≤ gaussianVisibilityMaxEigenvalue O a pole teacher := by
  let T := gaussianVisibilityOperator O a pole teacher
  have hb : BddAbove (Set.range (fun x : {x : Weight d // x ≠ 0} => T.rayleighQuotient x)) := by
    refine ⟨norm T, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (le_abs_self _).trans (T.rayleighQuotient_le_norm x)
  have hp : pole.val ≠ 0 := by
    intro hz
    have hn := unitSphere_norm pole
    simp only [hz, norm_zero] at hn
    norm_num at hn
  have hq : T.rayleighQuotient pole.val = 0 := by
    simp only [ContinuousLinearMap.rayleighQuotient, T, gaussianVisibilityOperator_quadratic,
      gaussianVisibilityMatrix_quadratic, gaussianTransverseVector_tangent, zero_pow (by decide : 2 ≠ 0),
      integral_zero, zero_div]
  exact hq ▸ le_ciSup hb ⟨pole.val,hp⟩

theorem gaussianVisibilityMaxEigenvalue_lower {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] :
    norm (gaussianTransverseMean O a pole teacher)^2 ≤ gaussianVisibilityMaxEigenvalue O a pole teacher := by
  by_cases hmean : gaussianTransverseMean O a pole teacher = 0
  · simpa only [hmean, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
      gaussianVisibilityMaxEigenvalue_nonneg O a pole teacher
  obtain ⟨s, _, _, _, _, hlo, _⟩ := gaussianVisibility_exists_top_eigenvector O a pole teacher hmean
  exact hlo

end PaperFormalization.MatrixFactorization
