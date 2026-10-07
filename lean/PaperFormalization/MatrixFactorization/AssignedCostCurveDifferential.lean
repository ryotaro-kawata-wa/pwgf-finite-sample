import PaperFormalization.MatrixFactorization.SphericalCurveCostDifferential
import PaperFormalization.MatrixFactorization.SphericalCurveCostAtPole
import PaperFormalization.MatrixFactorization.SphericalContraction
import PaperFormalization.MatrixFactorization.SphericalCharacteristics

/-! # The original assigned cost along an arbitrary spherical curve

The selected pole is locally constant inside either original cap. This local
fact is derived from continuity at the current time. No global continuity of
the assigned-pole map and no exponential-curve representation is required.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The original cap fixes the assigned pole throughout a time neighborhood. -/
theorem assignedPole_curve_eventually_constant {d : Nat} (a : UnitSphere d)
    (r : Real) (w : Real → UnitSphere d) (t : Real)
    (hr : r < Real.pi/2)
    (hw : w t ∈ sphericalCap a r ∪ sphericalCap (reflect a) r)
    (hc : ContinuousAt w t) :
    (fun s => assignedPole a (w s)) =ᶠ[𝓝 t] (fun _ => assignedPole a (w t)) := by
  rcases hw with hp | hn
  · have hnear : ∀ᶠ s in 𝓝 t, w s ∈ sphericalCap a r :=
      hc.eventually ((sphericalCap_isOpen a r).mem_nhds hp)
    filter_upwards [hnear] with s hs
    rw [assignedPole_positive a r hr hs,assignedPole_positive a r hr hp]
  · have hnear : ∀ᶠ s in 𝓝 t, w s ∈ sphericalCap (reflect a) r :=
      hc.eventually ((sphericalCap_isOpen (reflect a) r).mem_nhds hn)
    filter_upwards [hnear] with s hs
    rw [assignedPole_negative a r hr hs,assignedPole_negative a r hr hn]

/-- The original assigned cost agrees locally with the cost to the current pole. -/
theorem assignedCost_curve_eventually_poleCost {d : Nat} (a : UnitSphere d)
    (r : Real) (w : Real → UnitSphere d) (t : Real)
    (hr : r < Real.pi/2)
    (hw : w t ∈ sphericalCap a r ∪ sphericalCap (reflect a) r)
    (hc : ContinuousAt w t) :
    (fun s => assignedCost a (w s)) =ᶠ[𝓝 t]
      (fun s => poleCost (assignedPole a (w t)) (w s)) := by
  filter_upwards [assignedPole_curve_eventually_constant a r w t hr hw hc] with s hs
  simp only [assignedCost,poleCost,hs]

/-- The half-squared angular cost is differentiable along every differentiable
sphere curve on the open domain before the antipode, including its pole. -/
theorem poleCost_curve_hasDerivAt {d : Nat} (y : UnitSphere d)
    (w : Real → UnitSphere d) (v : Weight d) (t : Real)
    (hw : HasDerivAt (fun s => (w s).val) v t)
    (hs : sphericalDistance (w t) y < Real.pi) :
    HasDerivAt (fun s => poleCost y (w s))
      (inner Real (poleGradient y (w t)) v) t := by
  by_cases hy : w t = y
  · simpa only [hy,poleGradient_self,inner_zero_left] using
      poleCost_curve_hasDerivAt_at_pole y w v t hw hy
  · exact poleCost_curve_hasDerivAt_nonpole y w v t hw
      (sphericalDistance_pos_of_ne (w t) y (Ne.symm hy)) hs

/-- The derivative of the original assigned cost requires only membership of
the current point in the original caps, not a globally fixed assignment. -/
theorem assignedCost_curve_hasDerivAt {d : Nat} (a : UnitSphere d)
    (r : Real) (w : Real → UnitSphere d) (v : Weight d) (t : Real)
    (hr : r < Real.pi/2)
    (hw : w t ∈ sphericalCap a r ∪ sphericalCap (reflect a) r)
    (hd : HasDerivAt (fun s => (w s).val) v t) :
    HasDerivAt (fun s => assignedCost a (w s))
      (inner Real (assignedGradient a (w t)) v) t := by
  have hc : ContinuousAt w t := tendsto_subtype_rng.mpr hd.continuousAt
  have hs : sphericalDistance (w t) (assignedPole a (w t)) < Real.pi := by
    have hb := assignedPole_distance_lt_cap a r hr hw
    linarith [Real.pi_pos]
  exact (poleCost_curve_hasDerivAt (assignedPole a (w t)) w v t hd hs).congr_of_eventuallyEq
    (assignedCost_curve_eventually_poleCost a r w t hr hw hc)

/-- The original supported characteristic has cost derivative minus the
actual outward full-gradient pairing at every interior time. -/
theorem SphericalCharacteristicSolution.assignedCost_hasDerivAt
    {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
    {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
    {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (i : Fin 2) (w : UnitSphere d) (hw : w ∈ (initial i).support)
    (t : Real) (ht : t ∈ Ioo (0 : Real) T) :
    HasDerivAt (fun s => assignedCost pole (X.characteristic i s w))
      (-inner Real (sphericalObjectiveGradient O a pole lambda p
        (X.measure 0 t) (X.measure 1 t) teacher teacher i (X.characteristic i t w))
        (assignedGradient pole (X.characteristic i t w))) t := by
  have htc : t ∈ Icc (0 : Real) T := ⟨ht.1.le,ht.2.le⟩
  have hd := assignedCost_curve_hasDerivAt pole radius (fun s => X.characteristic i s w)
    _ t (X.cap i t htc).radius_lt (X.characteristic_mem_caps i t htc w hw) (X.ode i w hw t ht)
  simpa only [inner_neg_right,real_inner_comm] using hd

end PaperFormalization.MatrixFactorization
