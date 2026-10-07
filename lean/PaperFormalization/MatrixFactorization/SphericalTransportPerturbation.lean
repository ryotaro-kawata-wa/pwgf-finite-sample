import PaperFormalization.MatrixFactorization.AntipodalPotentialGeometry
import PaperFormalization.MatrixFactorization.SphericalTransport
import PaperFormalization.MatrixFactorization.SphericalRegularizerFlat

/-! # MF23: cap-free perturbation bounds for the actual transport value

Execution records: `MF23_VALIDATION.md`.

These statements require NO classical potential data,
NO transport optimizer, and NO cap membership. Push every feasible plan through
its first coordinate, compare the genuine angular costs, and then take the
original infimum. This provides a route for broader variational flows where
pointwise differentiability of a dual potential on an arbitrary support is
unavailable. The cost is not redefined by the comparison bound.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable def leftMapSphericalCoupling {d : Nat}
    {mu nu : Measure (UnitSphere d)} (gamma : SphericalCoupling mu nu)
    (f : UnitSphere d -> UnitSphere d) (hf : Measurable f) :
    SphericalCoupling (mu.map f) nu where
  measure := gamma.measure.map (fun z => (f z.1,z.2))
  first_marginal := by
    have hm : Measurable (fun z : UnitSphere d × UnitSphere d => (f z.1,z.2)) :=
      (hf.comp measurable_fst).prodMk measurable_snd
    rw [Measure.map_map measurable_fst hm]
    change gamma.measure.map (f ∘ Prod.fst) = _
    rw [<- Measure.map_map hf measurable_fst, gamma.first_marginal]
  second_marginal := by
    have hm : Measurable (fun z : UnitSphere d × UnitSphere d => (f z.1,z.2)) :=
      (hf.comp measurable_fst).prodMk measurable_snd
    rw [Measure.map_map measurable_snd hm]
    exact gamma.second_marginal

noncomputable def sphericalMapDisplacement {d : Nat} (mu : Measure (UnitSphere d))
    (f : UnitSphere d -> UnitSphere d) : Real :=
  integral mu (fun w => sphericalDistance (f w) w)

theorem sphericalMapDisplacement_integrable {d : Nat} (mu : Measure (UnitSphere d))
    [IsFiniteMeasure mu] (f : UnitSphere d -> UnitSphere d) (hf : Measurable f) :
    Integrable (fun w => sphericalDistance (f w) w) mu := by
  apply Integrable.of_bound
    (((sphericalDistance_continuous d).measurable.comp (hf.prodMk measurable_id)).aestronglyMeasurable)
    Real.pi
  exact Eventually.of_forall (fun w => by
    change norm (sphericalDistance (f w) w) ≤ Real.pi
    rw [Real.norm_eq_abs, abs_of_nonneg (sphericalDistance_nonneg _ _)]
    exact sphericalDistance_le_pi _ _)

theorem sphericalMapDisplacement_nonneg {d : Nat} (mu : Measure (UnitSphere d))
    (f : UnitSphere d -> UnitSphere d) : 0 <= sphericalMapDisplacement mu f :=
  integral_nonneg (fun w => sphericalDistance_nonneg _ _)

/-- Exact change-of-variables for a pushed feasible plan. -/
theorem sphericalTransportCost_leftMap {d : Nat} {mu nu : Measure (UnitSphere d)}
    (gamma : SphericalCoupling mu nu) (f : UnitSphere d -> UnitSphere d) (hf : Measurable f) :
    sphericalTransportCost (leftMapSphericalCoupling gamma f hf) =
      integral gamma.measure (fun z => (sphericalDistance (f z.1) z.2)^2) := by
  exact integral_map ((hf.comp measurable_fst).prodMk measurable_snd).aemeasurable
    ((sphericalDistance_continuous d).pow 2).aestronglyMeasurable

/-- Every feasible plan has the same displacement error, determined by its first marginal. -/
theorem sphericalTransportCost_leftMap_le {d : Nat} {mu nu : Measure (UnitSphere d)}
    [IsProbabilityMeasure mu] (gamma : SphericalCoupling mu nu)
    (f : UnitSphere d -> UnitSphere d) (hf : Measurable f) :
    sphericalTransportCost (leftMapSphericalCoupling gamma f hf) <=
      sphericalTransportCost gamma + 2*Real.pi*sphericalMapDisplacement mu f := by
  letI : IsProbabilityMeasure (mu.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  have hm : Measurable (fun z : UnitSphere d × UnitSphere d => (f z.1,z.2)) :=
    (hf.comp measurable_fst).prodMk measurable_snd
  have hi : Integrable (fun z : UnitSphere d × UnitSphere d => (sphericalDistance (f z.1) z.2)^2)
      gamma.measure := by
    apply (integrable_map_measure ((sphericalDistance_continuous d).pow 2).aestronglyMeasurable
      hm.aemeasurable).mp
    exact sphericalTransportCost_integrable (leftMapSphericalCoupling gamma f hf)
  have hd : Integrable (fun z : UnitSphere d × UnitSphere d => sphericalDistance (f z.1) z.1)
      gamma.measure := by
    apply (integrable_map_measure
      (((sphericalDistance_continuous d).measurable.comp (hf.prodMk measurable_id)).aestronglyMeasurable)
      measurable_fst.aemeasurable).mp
    rw [gamma.first_marginal]
    exact sphericalMapDisplacement_integrable mu f hf
  have hdisp : integral gamma.measure (fun z => sphericalDistance (f z.1) z.1) =
      sphericalMapDisplacement mu f := by
    simpa only [gamma.first_marginal, sphericalMapDisplacement] using
      (integral_map (μ := gamma.measure) (f := fun w => sphericalDistance (f w) w)
        measurable_fst.aemeasurable
        (((sphericalDistance_continuous d).measurable.comp
          (hf.prodMk measurable_id)).aestronglyMeasurable)).symm
  have hp (z : UnitSphere d × UnitSphere d) :
      (sphericalDistance (f z.1) z.2)^2 <= (sphericalDistance z.1 z.2)^2 +
        (2*Real.pi)*sphericalDistance (f z.1) z.1 := by
    have hh := (abs_le.mp (poleCost_sub_abs_le z.2 (f z.1) z.1)).2
    unfold poleCost at hh
    nlinarith
  have hb := integral_mono hi ((sphericalTransportCost_integrable gamma).add (hd.const_mul _)) hp
  simp only [Pi.add_apply] at hb
  rw [integral_add (sphericalTransportCost_integrable gamma) (hd.const_mul _),
    integral_const_mul, hdisp] at hb
  rw [sphericalTransportCost_leftMap]
  exact hb

/-- One-sided stability of the genuine infimum, with no attainment premise.
It remains valid for atomic laws and nonsmooth two-atom dual potentials. -/
theorem sphericalWassersteinSq_map_le {d : Nat}
    (mu nu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (f : UnitSphere d -> UnitSphere d) (hf : Measurable f) :
    sphericalWassersteinSq (mu.map f) nu <= sphericalWassersteinSq mu nu +
      2*Real.pi*sphericalMapDisplacement mu f := by
  letI : IsProbabilityMeasure (mu.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  have hh : sphericalWassersteinSq (mu.map f) nu - 2*Real.pi*sphericalMapDisplacement mu f <=
      sphericalWassersteinSq mu nu := by
    apply le_csInf (sphericalTransportValues_nonempty mu nu)
    rintro _ ⟨gamma, rfl⟩
    have hl := (sphericalWassersteinSq_le_cost (leftMapSphericalCoupling gamma f hf)).trans
      (sphericalTransportCost_leftMap_le gamma f hf)
    linarith
  linarith

/-- The same estimate for the exact sum of the two marginal costs. -/
theorem productAntipodalTransportSq_map_le {d : Nat} (pole : UnitSphere d)
    (mu : Fin 2 -> Measure (UnitSphere d)) (hmu : forall i, IsProbabilityMeasure (mu i))
    (f : Fin 2 -> UnitSphere d -> UnitSphere d) (hf : forall i, Measurable (f i)) :
    productAntipodalTransportSq pole ((mu 0).map (f 0)) ((mu 1).map (f 1)) <=
      productAntipodalTransportSq pole (mu 0) (mu 1) +
        2*Real.pi*(sphericalMapDisplacement (mu 0) (f 0) + sphericalMapDisplacement (mu 1) (f 1)) := by
  letI := hmu 0
  letI := hmu 1
  have h0 := sphericalWassersteinSq_map_le (mu 0) (antipodalMeasure pole) (f 0) (hf 0)
  have h1 := sphericalWassersteinSq_map_le (mu 1) (antipodalMeasure pole) (f 1) (hf 1)
  unfold productAntipodalTransportSq
  linarith

/-- Near zero, the actual EXP displacement equals |t| times the original L1 speed.
The common interval is supplied by compactness of the sphere, not by cap confinement. -/
theorem sphericalMapDisplacement_exp_near_zero {d : Nat}
    (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu]
    (v : UnitSphere d -> Weight d) (hv : forall w, inner Real w.val (v w) = 0)
    (hc : Continuous v) :
    ∀ᶠ t in nhds (0 : Real),
      sphericalMapDisplacement mu (sphericalExpFamily v hv t) =
        |t| * integral mu (fun w => norm (v w)) := by
  have hi := sphere_integrable mu _ hc.norm
  filter_upwards [eventually_uniform_short_tangent v hc] with t ht
  unfold sphericalMapDisplacement
  calc
    _ = integral mu (fun w => |t| * norm (v w)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun w => by
        change sphericalDistance (sphericalExpFamily v hv t w) w = |t| * norm (v w)
        rw [sphericalDistance_comm]
        change sphericalDistance w (sphericalExp w (t • v w) _) = _
        rw [sphericalDistance_exp w (t • v w) _ (ht w), norm_smul, Real.norm_eq_abs])
    _ = _ := integral_const_mul _ _

/-- Cap-free upper variation estimate. This does not presume the derivative exists. -/
theorem sphericalWassersteinSq_exp_upper_near_zero {d : Nat}
    (mu nu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (v : UnitSphere d -> Weight d) (hv : forall w, inner Real w.val (v w) = 0)
    (hc : Continuous v) :
    ∀ᶠ t in nhds (0 : Real),
      sphericalWassersteinSq (mu.map (sphericalExpFamily v hv t)) nu <=
        sphericalWassersteinSq mu nu + (2*Real.pi*integral mu (fun w => norm (v w)))*|t| := by
  filter_upwards [sphericalMapDisplacement_exp_near_zero mu v hv hc] with t ht
  have hm : Measurable (sphericalExpFamily v hv t) :=
    ((sphericalExpFamily_continuous v hv hc).comp (continuous_const.prodMk continuous_id)).measurable
  have hh := sphericalWassersteinSq_map_le mu nu (sphericalExpFamily v hv t) hm
  rw [ht] at hh
  convert hh using 1 <;> ring

end PaperFormalization.MatrixFactorization
