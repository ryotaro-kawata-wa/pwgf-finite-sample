import PaperFormalization.MatrixFactorization.ActiveHermiteFeature
open MeasureTheory
open PaperFormalization.MatrixFactorization
set_option synthInstance.maxHeartbeats 80000

-- Empty tensor orders and zero-dimensional contractions preserve their normalization.
example {d : Nat} (u v : Weight d) :
    inner Real (tensorPower 0 u) (tensorPower 0 v) = 1 := by rw [tensorPower_inner, pow_zero]
example {d n : Nat} : tensorTrace d n (0 : MomentTensor d (n + 2)) = 0 := map_zero _
example {n : Nat} (T : MomentTensor 0 (n + 2)) : tensorTrace 0 n T = 0 := by
  apply PiLp.ext
  intro I
  simp [tensorTrace_apply]
example {d k : Nat} (w : UnitSphere d) :
    tensorIteratedTrace d k 0 (tensorPower (k + 2 * 0) w.val) = tensorPower k w.val :=
  tensorIteratedTrace_unit 0 w
example {d k : Nat} (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu] :
    tensorIteratedTrace d k 2 (rawMoment mu (k + 2 * 2)) = rawMoment mu k :=
  tensorIteratedTrace_rawMoment 2 mu
example : (Polynomial.hermite 1).coeff 0 = 0 :=
  hermite_coeff_eq_zero_of_no_trace (by omega) (by omega)

-- The actual normalized Hermite features retain degrees zero and one, and zero input.
example {d : Nat} (z : Weight d) (w : UnitSphere d) :
    tensorHermiteEvaluation d 0 z (tensorPower 0 w.val) = 1 := by
  rw [tensorHermiteEvaluation_unit, normalizedHermite_zero]
example {d : Nat} (z : Weight d) (w : UnitSphere d) :
    tensorHermiteEvaluation d 1 z (tensorPower 1 w.val) = inner Real w.val z := by
  rw [tensorHermiteEvaluation_unit, normalizedHermite_one]
example {d n : Nat} (z : Weight d) : tensorHermiteEvaluation d n z 0 = 0 := map_zero _
example {d : Nat} (w : UnitSphere d) :
    tensorHermiteEvaluation d 1 0 (tensorPower 1 w.val) = 0 := by
  rw [tensorHermiteEvaluation_unit, normalizedHermite_one, inner_zero_right]

-- Empty active sets and zero coefficients do not require nondegeneracy assumptions.
example {d h : Nat} (a : Nat → Weight h) (z : Weight d) (X : ActiveMomentSpace d ∅) :
    activeHermiteFeature ∅ a z X = 0 := by simp [activeHermiteFeature_apply]
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (z : Weight d) :
    activeHermiteFeature O a z 0 = 0 := map_zero _
example {d h : Nat} (O : Finset Nat) (z : Weight d) (X : ActiveMomentSpace d O) :
    activeHermiteFeature O (fun _ => (0 : Weight h)) z X = 0 := by simp [activeHermiteFeature_apply]

-- Both reconstruction signs and finite, not necessarily probability, laws are covered.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (z : Weight d)
    (mu nu : Measure (UnitSphere d)) [IsFiniteMeasure mu] [IsFiniteMeasure nu] :
    activeHermiteFeature O a z (activeMomentMap O mu nu 0 + activeMomentMap O mu nu 1) =
      meanFeature (finiteHermiteActivation O a) mu z := activeHermiteFeature_left O a mu nu z
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (z : Weight d)
    (mu nu : Measure (UnitSphere d)) [IsFiniteMeasure mu] [IsFiniteMeasure nu] :
    activeHermiteFeature O a z (activeMomentMap O mu nu 0 - activeMomentMap O mu nu 1) =
      meanFeature (finiteHermiteActivation O a) nu z := activeHermiteFeature_right O a mu nu z
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (z : Weight d)
    (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu] :
    activeHermiteFeature O a z (rawActiveMoment O mu) =
      meanFeature (finiteHermiteActivation O a) mu z := activeHermiteFeature_rawMoment O a z mu
