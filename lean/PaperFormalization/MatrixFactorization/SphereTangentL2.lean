import PaperFormalization.MatrixFactorization.SphereFirstVariation
import Mathlib.MeasureTheory.Function.L2Space

/-! # MF28: the source L2 tangent space and its Borel representatives

This file uses the genuine L2 quotient for the original sphere law. Tangency
is an almost-everywhere condition. Orthogonal projection chooses a Borel,
everywhere-tangent representative without changing its equivalence class.
Nothing here selects representatives jointly in time or assumes a density.
Execution status is recorded in `MF28_WORKLOG.md`.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The source tangent condition is imposed on an L2 equivalence class. -/
noncomputable def sphereTangentL2 {d : Nat} (mu : Measure (UnitSphere d)) :
    Submodule Real (Lp (Weight d) 2 mu) where
  carrier := {v : Lp (Weight d) 2 mu | ∀ᵐ w ∂mu, inner Real w.val (v w) = 0}
  zero_mem' := by
    change ∀ᵐ w ∂mu, inner Real w.val ((0 : Lp (Weight d) 2 mu) w) = 0
    filter_upwards [Lp.coeFn_zero (Weight d) 2 mu] with w hw
    rw [hw]
    simp
  add_mem' := by
    intro v u hv hu
    change ∀ᵐ w ∂mu, inner Real w.val ((v + u : Lp (Weight d) 2 mu) w) = 0
    filter_upwards [Lp.coeFn_add v u, hv, hu] with w hw hvw huw
    simp only [hw, Pi.add_apply, inner_add_right, hvw, huw, add_zero]
  smul_mem' := by
    intro c v hv
    change ∀ᵐ w ∂mu, inner Real w.val ((c • v : Lp (Weight d) 2 mu) w) = 0
    filter_upwards [Lp.coeFn_smul c v, hv] with w hw hvw
    simp only [hw, Pi.smul_apply, real_inner_smul_right, hvw, mul_zero]

/-- A fixed-law representative; no pointwise meaning is assigned to the
unprojected L2 representative at exceptional labels. -/
noncomputable def sphereL2Representative {d : Nat} {mu : Measure (UnitSphere d)}
    (v : sphereTangentL2 mu) : UnitSphere d → Weight d :=
  tangentVersion (v : Lp (Weight d) 2 mu)

theorem sphereL2Representative_measurable {d : Nat} {mu : Measure (UnitSphere d)}
    (v : sphereTangentL2 mu) : Measurable (sphereL2Representative v) :=
  tangentVersion_measurable _ (Lp.stronglyMeasurable (v : Lp (Weight d) 2 mu)).measurable

theorem sphereL2Representative_tangent {d : Nat} {mu : Measure (UnitSphere d)}
    (v : sphereTangentL2 mu) (w : UnitSphere d) :
    inner Real w.val (sphereL2Representative v w) = 0 :=
  tangentVersion_tangent _ w

theorem sphereL2Representative_ae_eq {d : Nat} {mu : Measure (UnitSphere d)}
    (v : sphereTangentL2 mu) :
    sphereL2Representative v =ᵐ[mu] (v : Lp (Weight d) 2 mu) :=
  tangentVersion_ae_eq mu _ v.property

theorem sphereL2Representative_memLp {d : Nat} {mu : Measure (UnitSphere d)}
    (v : sphereTangentL2 mu) : MemLp (sphereL2Representative v) 2 mu :=
  (Lp.memLp (v : Lp (Weight d) 2 mu)).ae_eq (sphereL2Representative_ae_eq v).symm

theorem sphereL2Representative_norm_sq_integrable {d : Nat}
    {mu : Measure (UnitSphere d)} (v : sphereTangentL2 mu) :
    Integrable (fun w => norm (sphereL2Representative v w)^2) mu :=
  (memLp_two_iff_integrable_sq_norm
    (sphereL2Representative_measurable v).aestronglyMeasurable).mp
      (sphereL2Representative_memLp v)

/-- Both L2 factors are integrable as a pairing, even for a non-finite law. -/
theorem sphereL2Representative_pairing_integrable {d : Nat}
    {mu : Measure (UnitSphere d)} (g v : sphereTangentL2 mu) :
    Integrable (fun w => inner Real (sphereL2Representative g w)
      (sphereL2Representative v w)) mu := by
  apply (L2.integrable_inner (𝕜 := Real)
    (g : Lp (Weight d) 2 mu) (v : Lp (Weight d) 2 mu)).congr
  filter_upwards [sphereL2Representative_ae_eq g, sphereL2Representative_ae_eq v] with w hg hv
  rw [hg, hv]

/-- The Hilbert-space pairing is exactly the original-law Bochner integral. -/
theorem sphereL2Representative_inner {d : Nat} {mu : Measure (UnitSphere d)}
    (g v : sphereTangentL2 mu) :
    inner Real g v = ∫ w, inner Real (sphereL2Representative g w)
      (sphereL2Representative v w) ∂mu := by
  change inner Real (g : Lp (Weight d) 2 mu) (v : Lp (Weight d) 2 mu) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sphereL2Representative_ae_eq g, sphereL2Representative_ae_eq v] with w hg hv
  rw [hg, hv]

theorem BoundedTangentTest.memLp_two {d : Nat} (V : BoundedTangentTest d)
    (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu] : MemLp V.field 2 mu :=
  (memLp_two_iff_integrable_sq_norm V.measurable_field.aestronglyMeasurable).mpr
    (V.norm_sq_integrable mu)

/-- Every existing bounded Borel test defines a source L2 tangent direction. -/
noncomputable def BoundedTangentTest.toSphereL2 {d : Nat} (V : BoundedTangentTest d)
    (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu] : sphereTangentL2 mu :=
  ⟨(V.memLp_two mu).toLp V.field, by
    filter_upwards [(V.memLp_two mu).coeFn_toLp] with w hw
    rw [hw]
    exact V.tangent w⟩

theorem BoundedTangentTest.toSphereL2_ae_eq {d : Nat} (V : BoundedTangentTest d)
    (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu] :
    sphereL2Representative (V.toSphereL2 mu) =ᵐ[mu] V.field :=
  (sphereL2Representative_ae_eq (V.toSphereL2 mu)).trans (V.memLp_two mu).coeFn_toLp

theorem BoundedTangentTest.toSphereL2_pairing {d : Nat} (V : BoundedTangentTest d)
    (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu] (g : sphereTangentL2 mu) :
    inner Real g (V.toSphereL2 mu) =
      ∫ w, inner Real (sphereL2Representative g w) (V.field w) ∂mu := by
  rw [sphereL2Representative_inner]
  apply integral_congr_ae
  filter_upwards [V.toSphereL2_ae_eq mu] with w hw
  rw [hw]

end PaperFormalization.MatrixFactorization
