import PaperFormalization.MatrixFactorization.HilbertC2Chain
import PaperFormalization.MatrixFactorization.ActiveMomentCoordinates

/-! # MF36: finite gradient and Hessian suprema on the source active ball

These are the printed norms and degree coefficients for a supplied C2 active
functional. Identification of that functional with the actual fit polynomial
is an explicit separate obligation, not an assumption silently discharged here.
-/
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000

noncomputable def activeAntisymmetricPoint {d : Nat} {O : Finset Nat}
    (A : ActiveMomentSpace d O) : ActiveMomentCoordinates d O := WithLp.toLp 2 ![0, A]

noncomputable def activeGradientSup {d : Nat} {O : Finset Nat}
    (J : ActiveMomentCoordinates d O → Real) (R : Real) : Real :=
  sSup ((fun A : ActiveMomentSpace d O => ‖hilbertGradient J (activeAntisymmetricPoint A)‖) '' Metric.closedBall 0 R)

noncomputable def activeHessianSup {d : Nat} {O : Finset Nat}
    (J : ActiveMomentCoordinates d O → Real) (R : Real) : Real :=
  sSup ((fun A : ActiveMomentSpace d O => ‖hilbertHessian J (activeAntisymmetricPoint A)‖) '' Metric.closedBall 0 R)

noncomputable def activeC2CurvatureConstant {d : Nat} {O : Finset Nat}
    (J : ActiveMomentCoordinates d O → Real) (R : Real) : Real :=
  (∑ n ∈ O, (n : Real) ^ 2) * activeHessianSup J R +
    Real.sqrt (∑ n ∈ O, (n : Real) ^ 4) * activeGradientSup J R

/-- Compactness proves genuine boundedness of both sets used in the suprema. -/
theorem active_c2_suprema_bounded {d : Nat} {O : Finset Nat}
    (J : ActiveMomentCoordinates d O → Real) (hJ : ContDiff Real 2 J) (R : Real) :
    BddAbove ((fun A : ActiveMomentSpace d O => ‖hilbertGradient J (activeAntisymmetricPoint A)‖) '' Metric.closedBall 0 R) ∧
    BddAbove ((fun A : ActiveMomentSpace d O => ‖hilbertHessian J (activeAntisymmetricPoint A)‖) '' Metric.closedBall 0 R) := by
  letI : NormedSpace Real (ActiveMomentCoordinates d O) := PiLp.normedSpace 2 Real _
  have hp : Continuous (@activeAntisymmetricPoint d O) := by unfold activeAntisymmetricPoint; fun_prop
  have hG := ((hilbertGradient_contDiff J hJ).continuous.comp hp).norm
  have hH := (hilbertHessian_norm_continuous J hJ).comp hp
  exact ⟨((isCompact_closedBall (0 : ActiveMomentSpace d O) R).image hG).bddAbove,
    ((isCompact_closedBall (0 : ActiveMomentSpace d O) R).image hH).bddAbove⟩

/-- Pointwise domination and nonnegativity follow from an actual point in the ball. -/
theorem active_c2_suprema_bounds {d : Nat} {O : Finset Nat}
    (J : ActiveMomentCoordinates d O → Real) (hJ : ContDiff Real 2 J)
    (R : Real) (A : ActiveMomentSpace d O) (hA : ‖A‖ ≤ R) :
    ‖hilbertGradient J (activeAntisymmetricPoint A)‖ ≤ activeGradientSup J R ∧
    ‖hilbertHessian J (activeAntisymmetricPoint A)‖ ≤ activeHessianSup J R ∧
    0 ≤ activeGradientSup J R ∧ 0 ≤ activeHessianSup J R := by
  letI : NormedSpace Real (ActiveMomentCoordinates d O) := PiLp.normedSpace 2 Real _
  have hm : A ∈ Metric.closedBall (0 : ActiveMomentSpace d O) R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hA
  have hb := active_c2_suprema_bounded J hJ R
  have hG : ‖hilbertGradient J (activeAntisymmetricPoint A)‖ ≤ activeGradientSup J R :=
    le_csSup hb.1 ⟨A, hm, rfl⟩
  have hH : ‖hilbertHessian J (activeAntisymmetricPoint A)‖ ≤ activeHessianSup J R :=
    le_csSup hb.2 ⟨A, hm, rfl⟩
  exact ⟨hG, hH, (norm_nonneg _).trans hG, (hilbertHessian_norm_nonneg J _).trans hH⟩

/-- The source-shaped constant is nonnegative whenever the active ball has a point. -/
theorem activeC2CurvatureConstant_nonneg {d : Nat} {O : Finset Nat}
    (J : ActiveMomentCoordinates d O → Real) (hJ : ContDiff Real 2 J)
    (R : Real) (A : ActiveMomentSpace d O) (hA : ‖A‖ ≤ R) :
    0 ≤ activeC2CurvatureConstant J R := by
  letI : NormedSpace Real (ActiveMomentCoordinates d O) := PiLp.normedSpace 2 Real _
  have h := active_c2_suprema_bounds J hJ R A hA
  exact add_nonneg
    (mul_nonneg (Finset.sum_nonneg (fun n _ => sq_nonneg _)) h.2.2.2)
    (mul_nonneg (Real.sqrt_nonneg _) h.2.2.1)

end PaperFormalization.MatrixFactorization
