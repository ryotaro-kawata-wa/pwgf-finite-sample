import PaperFormalization.MatrixFactorization.SourceL2GradientBounds
import PaperFormalization.MatrixFactorization.NonnegativeIntegralCharacteristics
import PaperFormalization.MatrixFactorization.PrimalACCapRestriction

/-! # MF28: construct the existing AC class from L2 integral characteristics

The caller supplies actual integral characteristic equations and the source
L2 pairing identity. True velocity integrability, AC and the differential ODE
are derived from the actual objective bounds. The given
gradient representative is retained, including its measurable pullback.
No new flow record, cap condition, speed bound, or uniqueness premise is
introduced. The manuscript's precise characteristic-solution interpretation
is still an explicit correspondence obligation; see `MF28_WORKLOG.md`.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

variable {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
  (pole : UnitSphere d) (lambda p : Real) (teacher : Measure (UnitSphere d))
  (initial : Fin 2 → Measure (UnitSphere d))
  (hprob : ∀ i, IsProbabilityMeasure (initial i))
  (Phi : Fin 2 → Real → UnitSphere d → UnitSphere d)
  (hPhiM : ∀ i t, Measurable (Phi i t))
  (hPhiC : ∀ i t, 0 ≤ t → ContinuousOn (Phi i t) (initial i).support)
  (hPhi0 : ∀ i w, w ∈ (initial i).support → Phi i 0 w = w)
  (g : Fin 2 → Real → UnitSphere d → Weight d)
  (hgM : ∀ i t, Measurable (g i t))
  (hgPhiM : ∀ i, Measurable (fun tw : Real × UnitSphere d => g i tw.1 (Phi i tw.1 tw.2)))
  (hfirst : ∀ᵐ t ∂volume.restrict (Ici (0 : Real)), ∀ i,
    ∃ G : sphereTangentL2 ((initial i).map (Phi i t)),
      HasSphereL2FirstVariation ((initial i).map (Phi i t))
        (sourcePartialObjective O a pole lambda p
          (fun j => (initial j).map (Phi j t)) teacher i) G ∧
      sphereL2Representative G =ᵐ[(initial i).map (Phi i t)] g i t)
  (hintegral : ∀ i (n : Nat), ∀ᵐ w ∂initial i,
    ∀ t ∈ Icc (0 : Real) n,
      (Phi i t w).val = (Phi i 0 w).val - ∫ r in 0..t, g i r (Phi i r w))

/-- The actual first-variation speed bound supplies true time integrability.
The integral equations then supply AC and the AE differential ODE. -/
noncomputable def primalACOfIntegralL2 [IsProbabilityMeasure teacher]
    (hl : 0 ≤ lambda) (hp : 2 < p) :
    PrimalACCharacteristicData O a pole lambda p teacher initial := by
  have Hpv : ∀ᵐ t ∂volume.restrict (Ici (0 : Real)), ∀ i,
      HasSphereFirstVariation ((initial i).map (Phi i t))
        (sourcePartialObjective O a pole lambda p
          (fun j => (initial j).map (Phi j t)) teacher i) (g i t) := by
    filter_upwards [hfirst] with t ht
    intro i
    letI := hprob i
    letI : IsProbabilityMeasure ((initial i).map (Phi i t)) :=
      Measure.isProbabilityMeasure_map (hPhiM i t).aemeasurable
    obtain ⟨G, hG, hrep⟩ := ht i
    exact hG.to_primal_of_ae (g i t) (hgM i t) hrep
  have hspeed := source_primal_gradient_time_label_bound
    (volume.restrict (Ici (0 : Real))) O a pole lambda p hl hp initial hprob
      Phi hPhiM teacher g hgPhiM Hpv
  have hprefix : ∀ i (n : Nat), ∀ᵐ w ∂initial i,
      IntervalIntegrable (fun t => g i t (Phi i t w)) volume 0 n ∧
      ∀ t ∈ Icc (0 : Real) n,
        (Phi i t w).val = (Phi i 0 w).val - ∫ r in 0..t, g i r (Phi i r w) := by
    intro i n
    filter_upwards [hspeed i, hintegral i n] with w hb he
    refine ⟨?_, he⟩
    exact intervalIntegrable_of_nonnegative_ae_bound (fun t => g i t (Phi i t w))
      ((hgPhiM i).comp (measurable_id.prodMk measurable_const))
      (primalObjectiveSpeedBound d O a lambda p) hb le_rfl (Nat.cast_nonneg n)
  exact {
    initial_probability := hprob
    characteristic := Phi
    measurable_space := hPhiM
    continuous_space := hPhiC
    initial_map := hPhi0
    gradient := g
    measurable_pullback := hgPhiM
    first_variation := Hpv
    path_ac := fun i s t hs ht =>
      (ae_integral_characteristic_regular (initial i)
        (fun t w => (Phi i t w).val) (fun t w => g i t (Phi i t w)) (hprefix i)).1 s t hs ht
    ode := fun i =>
      (ae_integral_characteristic_regular (initial i)
        (fun t w => (Phi i t w).val) (fun t w => g i t (Phi i t w)) (hprefix i)).2 }

@[simp] theorem primalACOfIntegralL2_characteristic [IsProbabilityMeasure teacher]
    (hl : 0 ≤ lambda) (hp : 2 < p) :
    (primalACOfIntegralL2 O a pole lambda p teacher initial hprob Phi
      hPhiM hPhiC hPhi0 g hgM hgPhiM hfirst hintegral hl hp).characteristic = Phi := rfl

@[simp] theorem primalACOfIntegralL2_gradient [IsProbabilityMeasure teacher]
    (hl : 0 ≤ lambda) (hp : 2 < p) :
    (primalACOfIntegralL2 O a pole lambda p teacher initial hprob Phi
      hPhiM hPhiC hPhi0 g hgM hgPhiM hfirst hintegral hl hp).gradient = g := rfl

@[simp] theorem primalACOfIntegralL2_measure [IsProbabilityMeasure teacher]
    (hl : 0 ≤ lambda) (hp : 2 < p) :
    (primalACOfIntegralL2 O a pole lambda p teacher initial hprob Phi
      hPhiM hPhiC hPhi0 g hgM hgPhiM hfirst hintegral hl hp).measure =
        fun i t => (initial i).map (Phi i t) := rfl

include hprob hPhiM hPhiC hPhi0 hgM hgPhiM hfirst hintegral

/-- The same integral characteristics yield a positive initial cap interval
and the existing all-support classical record. AC, pointwise canonical ODE,
cap preservation, and the interval length are outputs, not extra inputs. -/
theorem integral_l2_classical_first_cap [IsProbabilityMeasure teacher]
    (hl : 0 ≤ lambda) (hp : 2 < p)
    (r : Real) (hc : ∀ i, TwoCapClass pole r (initial i)) :
    let tau := primalInitialCapTime d O a pole r lambda p initial
    0 < tau ∧
    ∃ Y : SphericalCharacteristicSolution O a pole r lambda p teacher initial tau,
      Y.measure = (fun i t => (initial i).map (Phi i t)) ∧ Y.characteristic = Phi := by
  let X := primalACOfIntegralL2 O a pole lambda p teacher initial hprob Phi
    hPhiM hPhiC hPhi0 g hgM hgPhiM hfirst hintegral hl hp
  obtain ⟨htau, Y, hmeasure, hcharacteristic, _⟩ :=
    primal_ac_classical_first_cap X hl hp r hc
  exact ⟨htau, Y, hmeasure, hcharacteristic⟩

end PaperFormalization.MatrixFactorization
