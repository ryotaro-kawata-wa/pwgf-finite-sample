import PaperFormalization.MatrixFactorization.PrimalACWeakContinuity
import Mathlib.Analysis.InnerProductSpace.Dual

/-! # MF31: intrinsic spherical gradients of weak test functions

Riesz representation and tangent projection recover the spherical test
pairing from the ambient differential. The original velocity is tangent
only under its current law at the source's AE times; those quantifiers are
retained in the continuity equation.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def sphericalTestGradient {d : Nat} (phi : Weight d → Real)
    (w : UnitSphere d) : Weight d :=
  transverseProjection w ((InnerProductSpace.toDual Real (Weight d)).symm (fderiv Real phi w.val))

theorem sphericalTestGradient_tangent {d : Nat} (phi : Weight d → Real) (w : UnitSphere d) :
    inner Real w.val (sphericalTestGradient phi w) = 0 := transverseProjection_tangent _ _

/-- Pairing with a tangent velocity is exactly the ambient differential. -/
theorem sphericalTestGradient_pairing {d : Nat} (phi : Weight d → Real)
    (w : UnitSphere d) (v : Weight d) (hv : inner Real w.val v = 0) :
    inner Real (sphericalTestGradient phi w) v = fderiv Real phi w.val v := by
  unfold sphericalTestGradient
  rw [real_inner_comm, transverseProjection_pairing w v _ hv, real_inner_comm]
  exact InnerProductSpace.toDual_symm_apply

theorem sphericalTestGradient_continuous {d : Nat} (phi : Weight d → Real)
    (hphi : ContDiff Real 1 phi) : Continuous (sphericalTestGradient phi) := by
  have hg : Continuous (fun w : UnitSphere d =>
      (InnerProductSpace.toDual Real (Weight d)).symm (fderiv Real phi w.val)) :=
    (InnerProductSpace.toDual Real (Weight d)).symm.continuous.comp
      ((hphi.continuous_fderiv (by decide)).comp continuous_subtype_val)
  exact hg.sub ((continuous_subtype_val.inner (𝕜 := Real) hg).smul continuous_subtype_val)

variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

/-- The intrinsic and ambient fluxes coincide with true spatial integrability. -/
theorem PrimalACCharacteristicData.sphericalTestFlux_ae
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (phi : Weight d → Real) (hphi : ContDiff Real 1 phi) (i : Fin 2) :
    ∀ᵐ t ∂volume.restrict (Ici (0 : Real)),
      Integrable (fun w => inner Real (sphericalTestGradient phi w) (X.gradient i t w))
        (X.measure i t) ∧
      X.currentTestFlux phi i t =
        ∫ w, inner Real (sphericalTestGradient phi w) (X.gradient i t w) ∂X.measure i t := by
  filter_upwards [X.first_variation, X.currentTestFlux_integrable_ae phi hphi i] with t ht hint
  have he : (fun w => fderiv Real phi w.val (X.gradient i t w)) =ᵐ[X.measure i t]
      fun w => inner Real (sphericalTestGradient phi w) (X.gradient i t w) := by
    filter_upwards [(ht i).tangent_ae] with w hw
    exact (sphericalTestGradient_pairing phi w (X.gradient i t w) hw).symm
  exact ⟨hint.congr he, integral_congr_ae he⟩

/-- The weak continuity equation in the source's intrinsic spherical notation. -/
theorem PrimalACCharacteristicData.spherical_weak_continuity_ae
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (phi : Weight d → Real) (hphi : ContDiff Real 1 phi) (i : Fin 2) :
    ∀ᵐ t ∂volume.restrict (Ici (0 : Real)),
      Integrable (fun w => inner Real (sphericalTestGradient phi w) (X.gradient i t w))
        (X.measure i t) ∧
      HasDerivAt (fun r => ∫ w, phi w.val ∂X.measure i r)
        (-(∫ w, inner Real (sphericalTestGradient phi w) (X.gradient i t w) ∂X.measure i t)) t := by
  filter_upwards [X.sphericalTestFlux_ae phi hphi i,
    X.weak_continuity_ae hl hp phi hphi i] with t hs hd
  refine ⟨hs.1, ?_⟩
  have hder := hd.2
  change HasDerivAt _ (-X.currentTestFlux phi i t) t at hder
  rw [hs.2] at hder
  exact hder

end PaperFormalization.MatrixFactorization
