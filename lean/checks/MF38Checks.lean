import PaperFormalization.MatrixFactorization.ActiveGaussianFitPolynomial
open MeasureTheory ProbabilityTheory
open PaperFormalization.MatrixFactorization
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

-- All natural Gaussian moments remain available, including zero powers and zero tensors.
example (d n : Nat) : 0 ≤ tensorHermiteMass d n := tensorHermiteMass_nonneg d n
example {d n : Nat} (T : MomentTensor d n) :
    Integrable (fun z : Weight d => ‖tensorHermiteEvaluation d n z T‖ ^ 0)
      (stdGaussian (Weight d)) := tensorHermiteEvaluation_gaussian_power_integrable T 0
example {d : Nat} (T : MomentTensor d 0) :
    Integrable (fun z : Weight d => ‖tensorHermiteEvaluation d 0 z T‖ ^ 4)
      (stdGaussian (Weight d)) := tensorHermiteEvaluation_gaussian_power_integrable T 4
example {d n : Nat} : Integrable (fun z : Weight d =>
    ‖tensorHermiteEvaluation d n z (0 : MomentTensor d n)‖ ^ 8) (stdGaussian (Weight d)) :=
  tensorHermiteEvaluation_gaussian_power_integrable 0 8
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) :
    Integrable (fun z : Weight d => ‖activeHermiteFeature O a z‖ ^ 4) (stdGaussian (Weight d)) :=
  activeHermiteFeature_operator_power_integrable O a 4
example {d h : Nat} (a : Nat → Weight h) :
    activeTensorFeatureMass (d := d) ∅ a = 0 := by simp [activeTensorFeatureMass]

-- The four-linear form is the actual matrix pairing, with no dimension assumption.
example {h : Nat} (u v x y : Weight h) :
    outerQuartic h ![u,v,x,y] = inner Real (outer u v) (outer x y) :=
  outerQuartic_eq_matrix_pairing _
example {h : Nat} (v x y : Weight h) : outerQuartic h ![0,v,x,y] = 0 := by
  simp [outerQuartic_apply]
example {h : Nat} (u v : Weight h) : outerQuartic h ![u,v,u,v] = ‖outer u v‖ ^ 2 := by
  rw [outerQuartic_eq_matrix_pairing]
  change inner Real (outer u v) (outer u v) = _
  exact real_inner_self_eq_norm_sq _
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (X : Fin 4 → ActiveMomentSpace d O) :
    Integrable (fun z : Weight d =>
      inner Real (activeHermiteFeature O a z (X 0)) (activeHermiteFeature O a z (X 2)) *
      inner Real (activeHermiteFeature O a z (X 1)) (activeHermiteFeature O a z (X 3)))
      (stdGaussian (Weight d)) := activeQuartic_scalar_integrable O a X
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (X : Fin 4 → ActiveMomentSpace d O) :
    activeGaussianQuartic O a X = ∫ z : Weight d,
      inner Real (activeHermiteFeature O a z (X 0)) (activeHermiteFeature O a z (X 2)) *
      inner Real (activeHermiteFeature O a z (X 1)) (activeHermiteFeature O a z (X 3))
      ∂stdGaussian (Weight d) := activeGaussianQuartic_apply O a X
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) :
    activeGaussianQuartic (d := d) O a (fun _ => 0) = 0 :=
  (activeGaussianQuartic (d := d) O a).map_coord_zero 0 rfl

-- The actual fit polynomial is smooth and nonnegative on arbitrary, possibly unrealizable, tensors.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (teacher : ActiveMomentSpace d O) :
    ContDiff Real 2 (activeFittingPolynomial O a teacher) :=
  (activeFittingPolynomial_contDiff O a teacher).of_le (by simp)
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (teacher : ActiveMomentSpace d O) (X : ActiveMomentCoordinates d O) :
    0 ≤ activeFittingPolynomial O a teacher X := activeFittingPolynomial_nonneg O a teacher X
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) :
    activeFittingPolynomial (d := d) O a 0 0 = 0 := by
  rw [activeFittingPolynomial_eq_fittingEnergy]
  simp [fittingEnergy]
example {d h : Nat} (O : Finset Nat) (teacher : ActiveMomentSpace d O)
    (X : ActiveMomentCoordinates d O) :
    activeFittingPolynomial O (fun _ => (0 : Weight h)) teacher X = 0 := by
  rw [activeFittingPolynomial_eq_fittingEnergy]
  simp [activeHermiteFeature_apply, fittingEnergy]
example {d h : Nat} (a : Nat → Weight h) (teacher : ActiveMomentSpace d ∅)
    (X : ActiveMomentCoordinates d ∅) : activeFittingPolynomial ∅ a teacher X = 0 := by
  rw [activeFittingPolynomial_eq_fittingEnergy]
  simp [activeHermiteFeature_apply, fittingEnergy]
example {d : Nat} (O : Finset Nat) (a : Nat → Weight 0)
    (teacher : ActiveMomentSpace d O) (X : ActiveMomentCoordinates d O) :
    activeFittingPolynomial O a teacher X = 0 := by
  rw [activeFittingPolynomial_eq_fittingEnergy]
  simp [fittingEnergy, Subsingleton.elim (outer _ _) (0 : Output 0)]

-- Finite laws need not be probability measures; exact teacher fitting is still zero.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (teacher mu nu : Measure (UnitSphere d))
    [IsFiniteMeasure teacher] [IsFiniteMeasure mu] [IsFiniteMeasure nu] :
    activeFittingPolynomial O a (rawActiveMoment O teacher) (activeMomentMap O mu nu) =
      fittingEnergy (stdGaussian (Weight d))
        (fun z => outer (meanFeature (finiteHermiteActivation O a) teacher z)
          (meanFeature (finiteHermiteActivation O a) teacher z))
        (meanFeature (finiteHermiteActivation O a) mu)
        (meanFeature (finiteHermiteActivation O a) nu) :=
  activeFittingPolynomial_original_measures O a teacher mu nu
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (teacher : Measure (UnitSphere d)) [IsFiniteMeasure teacher] :
    activeFittingPolynomial O a (rawActiveMoment O teacher) (activeMomentMap O teacher teacher) = 0 := by
  rw [activeFittingPolynomial_original_measures, fittingEnergy_exact]
