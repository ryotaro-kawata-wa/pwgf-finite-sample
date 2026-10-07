import PaperFormalization.MatrixFactorization.PrimalACIntegralForm
import PaperFormalization.MatrixFactorization.PrimalACContinuousTests
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Integral.Prod

/-! # MF29: smooth tests along the original primal AC characteristics

The source continuity equation is tested against ambient C1 functions
restricted to the sphere. Compactness supplies the required derivative
bound. The auxiliary ambient extension is used only to establish joint
measurability, and equals the original path on nonnegative supported labels.
No cap hypothesis or replacement of the original gradient is introduced.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- A C1 test has a finite operator-norm derivative bound on the unit ball. -/
theorem smooth_test_derivative_bound {d : Nat} (phi : Weight d → Real)
    (hphi : ContDiff Real 1 phi) :
    ∃ C : Real, 0 ≤ C ∧ ∀ x : Weight d, norm x ≤ 1 → norm (fderiv Real phi x) ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Weight d) 1).exists_bound_of_continuousOn
    (hphi.continuous_fderiv (by decide)).continuousOn
  refine ⟨|C|, abs_nonneg _, ?_⟩
  intro x hx
  exact (hC x (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)).trans
    (le_abs_self C)

variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

/-- The zero extension has no role in defining the actual flow or its law. -/
noncomputable def PrimalACCharacteristicData.supportedAmbient
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (i : Fin 2) (t : Real) (w : UnitSphere d) : Weight d := by
  classical
  exact if 0 ≤ t ∧ w ∈ (initial i).support then (X.characteristic i t w).val else 0

@[simp] theorem PrimalACCharacteristicData.supportedAmbient_eq
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (i : Fin 2) (t : Real) (ht : 0 ≤ t) (w : UnitSphere d)
    (hw : w ∈ (initial i).support) :
    X.supportedAmbient i t w = (X.characteristic i t w).val := by
  simp only [PrimalACCharacteristicData.supportedAmbient, ht, hw, and_self, if_true]

theorem PrimalACCharacteristicData.supportedAmbient_measurable
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p) (i : Fin 2) :
    Measurable (fun tw : Real × UnitSphere d => X.supportedAmbient i tw.1 tw.2) := by
  classical
  change Measurable (((Ici (0 : Real)) ×ˢ (initial i).support).piecewise
    (fun tw : Real × UnitSphere d => (X.characteristic i tw.1 tw.2).val) (fun _ => 0))
  exact (continuous_subtype_val.comp_continuousOn
    (X.supported_joint_continuity hl hp i)).measurable_piecewise continuousOn_const
      (measurableSet_Ici.prod (Measure.isClosed_support (μ := initial i)).measurableSet)

theorem PrimalACCharacteristicData.supportedAmbient_norm_le
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (i : Fin 2) (t : Real) (w : UnitSphere d) : norm (X.supportedAmbient i t w) ≤ 1 := by
  classical
  unfold PrimalACCharacteristicData.supportedAmbient
  split_ifs <;> simp

/-- A positive-sign flux, so the negative-gradient ODE has derivative minus flux. -/
noncomputable def PrimalACCharacteristicData.testFlux
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (phi : Weight d → Real) (i : Fin 2) (t : Real) (w : UnitSphere d) : Real :=
  fderiv Real phi (X.supportedAmbient i t w) (X.pullbackGradient i t w)

theorem PrimalACCharacteristicData.testFlux_measurable
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (phi : Weight d → Real) (hphi : ContDiff Real 1 phi) (i : Fin 2) :
    Measurable (fun tw : Real × UnitSphere d => X.testFlux phi i tw.1 tw.2) :=
  (hphi.continuous_fderiv_apply (by decide)).measurable.comp
    ((X.supportedAmbient_measurable hl hp i).prodMk (X.measurable_pullback i))

/-- AC of the scalar test is derived from supported time Lipschitz regularity. -/
theorem PrimalACCharacteristicData.smoothTest_ac
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (phi : Weight d → Real) (hphi : ContDiff Real 1 phi)
    (i : Fin 2) (w : UnitSphere d) (hw : w ∈ (initial i).support)
    (s t : Real) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    AbsolutelyContinuousOnInterval (fun r => phi (X.characteristic i r w).val) s t := by
  obtain ⟨K, hK⟩ := hphi.contDiffOn.exists_lipschitzOnWith (by decide)
    (convex_closedBall (0 : Weight d) 1) (isCompact_closedBall (0 : Weight d) 1)
  have hpath : LipschitzOnWith (Real.nnabs (primalObjectiveSpeedBound d O a lambda p))
      (fun r => (X.characteristic i r w).val) (uIcc s t) := by
    apply lipschitzOnWith_iff_dist_le_mul.mpr
    intro u hu v hv
    exact (X.supported_lipschitz hl hp i w hw).dist_le_mul
      u ((le_min hs ht).trans hu.1) v ((le_min hs ht).trans hv.1)
  have hmap : MapsTo (fun r => (X.characteristic i r w).val) (uIcc s t)
      (Metric.closedBall (0 : Weight d) 1) := by
    intro r hr
    simp only [Metric.mem_closedBall, dist_zero_right, unitSphere_norm, le_refl]
  exact (hK.comp hpath hmap).absolutelyContinuousOnInterval

/-- The AE ODE yields the chain rule for the actual C1 test, without caps. -/
theorem PrimalACCharacteristicData.smoothTest_ae_deriv
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (phi : Weight d → Real) (hphi : ContDiff Real 1 phi) (i : Fin 2) :
    ∀ᵐ w ∂initial i, ∀ᵐ t ∂volume.restrict (Ici (0 : Real)),
      HasDerivAt (fun r => phi (X.characteristic i r w).val) (-X.testFlux phi i t w) t := by
  filter_upwards [X.ode i, Measure.support_mem_ae (μ := initial i)] with w hd hw
  filter_upwards [hd, ae_restrict_mem measurableSet_Ici] with t ht htime
  have hD := ((hphi.differentiable (by decide))
    (X.characteristic i t w).val).hasFDerivAt.comp_hasDerivAt t ht
  convert hD using 1 <;>
    first | rfl | simp only [PrimalACCharacteristicData.testFlux,
      X.supportedAmbient_eq i t htime w hw,
      PrimalACCharacteristicData.pullbackGradient, map_neg]

end PaperFormalization.MatrixFactorization
