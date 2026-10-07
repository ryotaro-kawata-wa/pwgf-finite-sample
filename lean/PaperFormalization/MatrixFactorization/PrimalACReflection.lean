import PaperFormalization.MatrixFactorization.PrimalFirstVariationSymmetry
import PaperFormalization.MatrixFactorization.PrimalACCapRestriction

/-! # MF27: reflection/exchange of one complete primal AC trajectory

Verification status and conditional scope: see `MF27_VALIDATION.md`. Every field of the unchanged MF25 class is
transformed: actual pushed laws, primal variation, jointly Borel pullback,
original-label AE absolute continuity and AE ODE. No cap condition, dual
potential, all-supported derivative, or uniqueness is assumed here.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

noncomputable def PrimalACCharacteristicData.reflectionCharacteristic
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (i : Fin 2) (t : Real) (w : UnitSphere d) : UnitSphere d :=
  reflect (X.characteristic i.rev t (reflect w))

noncomputable def PrimalACCharacteristicData.reflectionGradient
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (i : Fin 2) (t : Real) (w : UnitSphere d) : Weight d :=
  -X.gradient i.rev t (reflect w)

/-- The transformed law is an equality of the original measurable pushforwards. -/
theorem PrimalACCharacteristicData.reflectionMeasure_eq
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (i : Fin 2) (t : Real) :
    (reflectionExchangePair initial i).map (X.reflectionCharacteristic i t) =
      reflectedMeasure (X.measure i.rev t) :=
  reflectedMeasure_map_conjugate (initial i.rev) (X.characteristic i.rev t)
    (X.measurable_space i.rev t)

/-- Joint Borel regularity is inherited by composition, not from separate measurability. -/
theorem PrimalACCharacteristicData.reflectionPullback_measurable
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial) (i : Fin 2) :
    Measurable (fun tw : Real × UnitSphere d =>
      X.reflectionGradient i tw.1 (X.reflectionCharacteristic i tw.1 tw.2)) := by
  have hm := (X.measurable_pullback i.rev).comp
    (measurable_fst.prodMk ((reflect_measurable d).comp measurable_snd))
  simpa only [PrimalACCharacteristicData.reflectionGradient,
    PrimalACCharacteristicData.reflectionCharacteristic, reflect_reflect,
    Function.comp_def, Pi.neg_def] using hm.neg

/-- Primal covariance holds at exactly the original Lebesgue-AE nonnegative times. -/
theorem PrimalACCharacteristicData.reflectionFirstVariation
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (hO : ∀ n ∈ O, Odd n) :
    ∀ᵐ t ∂volume.restrict (Ici (0 : Real)), ∀ i,
      HasSphereFirstVariation
        ((reflectionExchangePair initial i).map (X.reflectionCharacteristic i t))
        (sourcePartialObjective O a pole lambda p
          (fun j => (reflectionExchangePair initial j).map (X.reflectionCharacteristic j t))
          teacher i) (X.reflectionGradient i t) := by
  filter_upwards [X.first_variation] with t ht
  have hs := source_primal_firstVariation_reflection_exchange O a hO pole lambda p
    (fun j => X.measure j t) (fun j => X.measure_probability j t) teacher
    (fun j => X.gradient j t) ht
  have hlaws : (fun j => (reflectionExchangePair initial j).map
      (X.reflectionCharacteristic j t)) = reflectionExchangePair (fun j => X.measure j t) := by
    funext j
    exact X.reflectionMeasure_eq j t
  intro i
  rw [hlaws, X.reflectionMeasure_eq]
  exact hs i

/-- A genuine global primal AC trajectory for the reflected/exchanged initial data. -/
noncomputable def PrimalACCharacteristicData.reflectionExchange
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (hO : ∀ n ∈ O, Odd n) :
    PrimalACCharacteristicData O a pole lambda p teacher (reflectionExchangePair initial) where
  initial_probability := by
    intro i
    letI := X.initial_probability i.rev
    exact reflectedMeasure_probability (initial i.rev)
  characteristic := X.reflectionCharacteristic
  measurable_space := by
    intro i t
    exact (reflect_measurable d).comp
      ((X.measurable_space i.rev t).comp (reflect_measurable d))
  continuous_space := by
    intro i t ht
    apply (reflect_continuous d).comp_continuousOn
    apply (X.continuous_space i.rev t ht).comp (reflect_continuous d).continuousOn
    intro w hw
    exact (reflectedMeasure_mem_support (initial i.rev) w).mp hw
  initial_map := by
    intro i w hw
    have hw' := (reflectedMeasure_mem_support (initial i.rev) w).mp hw
    change reflect (X.characteristic i.rev 0 (reflect w)) = w
    rw [X.initial_map i.rev (reflect w) hw', reflect_reflect]
  gradient := X.reflectionGradient
  measurable_pullback := X.reflectionPullback_measurable
  first_variation := X.reflectionFirstVariation hO
  path_ac := by
    intro i s t hs ht
    filter_upwards [ae_reflected_of_ae (initial i.rev) (X.path_ac i.rev s t hs ht)] with w hw
    simpa only [PrimalACCharacteristicData.reflectionCharacteristic, reflect_val,
      Pi.neg_def] using hw.neg
  ode := by
    intro i
    filter_upwards [ae_reflected_of_ae (initial i.rev) (X.ode i.rev)] with w hw
    filter_upwards [hw] with t ht
    simpa only [PrimalACCharacteristicData.reflectionCharacteristic,
      PrimalACCharacteristicData.reflectionGradient, reflect_val, reflect_reflect,
      Pi.neg_def, neg_neg] using ht.neg

@[simp] theorem PrimalACCharacteristicData.reflectionExchange_characteristic
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (hO : ∀ n ∈ O, Odd n) (i : Fin 2) (t : Real) (w : UnitSphere d) :
    (X.reflectionExchange hO).characteristic i t w =
      reflect (X.characteristic i.rev t (reflect w)) := rfl

@[simp] theorem PrimalACCharacteristicData.reflectionExchange_gradient
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (hO : ∀ n ∈ O, Odd n) (i : Fin 2) (t : Real) (w : UnitSphere d) :
    (X.reflectionExchange hO).gradient i t w = -X.gradient i.rev t (reflect w) := rfl

@[simp] theorem PrimalACCharacteristicData.reflectionExchange_measure
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (hO : ∀ n ∈ O, Odd n) (i : Fin 2) (t : Real) :
    (X.reflectionExchange hO).measure i t = reflectedMeasure (X.measure i.rev t) :=
  X.reflectionMeasure_eq i t

/-- Involution of the actual maps, without equating irrelevant representation proofs. -/
@[simp] theorem PrimalACCharacteristicData.reflectionExchange_twice_characteristic
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (hO : ∀ n ∈ O, Odd n) (i : Fin 2) (t : Real) (w : UnitSphere d) :
    ((X.reflectionExchange hO).reflectionExchange hO).characteristic i t w =
      X.characteristic i t w := by
  simp only [PrimalACCharacteristicData.reflectionExchange_characteristic,
    Fin.rev_rev, reflect_reflect]

end PaperFormalization.MatrixFactorization
