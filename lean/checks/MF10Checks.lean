import PaperFormalization.MatrixFactorization.GeneralRetractionObjective
import PaperFormalization.MatrixFactorization.GeneralRetractionTime
import PaperFormalization.MatrixFactorization.GeneralRetractionFittingVariation
import PaperFormalization.MatrixFactorization.GeneralRetractionRegularizerFlat

/-! Boundary checks for the general normalized path and its actual Gaussian fit.
These checks include actual angular transport and the fractional-power
regularizer, after their source-level derivative exchanges were compiled. -/
open MeasureTheory ProbabilityTheory Set Filter Asymptotics
open scoped Topology
open PaperFormalization.MatrixFactorization
set_option autoImplicit false

-- The removable zero-speed branch retains all signed times.
example (t : Real) : retractionTime 0 t = t := retractionTime_zero_speed t
example (speed t : Real) : retractionTime speed (-t) = -retractionTime speed t := by
  by_cases hs : speed = 0
  · simp [hs]
  · simp [retractionTime, hs, neg_mul, Real.arctan_neg, neg_div]

-- Zero velocity is a constant actual normalized sphere path, including its
-- all-time first and second ambient derivatives.
example {d : Nat} (w : UnitSphere d) (t : Real) :
    sphericalRetractVector w 0 t = w.val := by simp [sphericalRetractVector]
example {d : Nat} (w : UnitSphere d) (t : Real) :
    sphericalRetractVelocity w 0 t = 0 := by
  apply norm_eq_zero.mp
  exact le_antisymm (by simpa using sphericalRetractVelocity_norm_le w 0 (by simp) t) (norm_nonneg _)
example {d : Nat} (w : UnitSphere d) (t : Real) :
    sphericalRetractAcceleration w 0 t = 0 := by
  apply norm_eq_zero.mp
  exact le_antisymm (by simpa using sphericalRetractAcceleration_norm_le w 0 (by simp) t) (norm_nonneg _)
example {d : Nat} (w : UnitSphere d) (v : Weight d) :
    sphericalRetractAcceleration w v 0 = -(norm v^2) • w.val :=
  sphericalRetractAcceleration_zero w v
example (speed : Real) : deriv (deriv (retractionTime speed)) 0 = 0 :=
  (retractionTime_second_zero speed).deriv

-- The exact angle is spherical, and both time directions stay in the original
-- open hemisphere at every finite time.
example {d : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (t : Real) :
    sphericalDistance w (sphericalRetract w v hv (-t)) = abs (Real.arctan (t*norm v)) := by
  rw [sphericalDistance_retract]
  simp only [neg_mul, Real.arctan_neg, abs_neg]
example {d : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (t : Real) :
    sphericalDistance w (sphericalRetract w v hv t) < Real.pi/2 := by
  rw [sphericalDistance_retract]
  exact abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩

-- The initial second feature jet retains the radial acceleration term.
example {d h : Nat} (k : Nat) (O : Finset Nat) (a : Nat → Weight h)
    (w : UnitSphere d) (z : Weight d) :
    retractedFeatureFirst k O a w 0 (by simp) z 0 = 0 := by simp
example {d h : Nat} (k : Nat) (O : Finset Nat) (a : Nat → Weight h)
    (w : UnitSphere d) (v : Weight d) (hv : inner Real w.val v = 0) (z : Weight d) :
    retractedFeatureSecond k O a w v hv z 0 =
      (inner Real v z)^2 • finiteHermiteActivationJet (k+2) O a (inner Real w.val z) -
        (norm v^2*inner Real w.val z) • finiteHermiteActivationJet (k+1) O a (inner Real w.val z) :=
  retractedFeatureSecond_at_zero k O a w v hv z
example {d h : Nat} (k : Nat) (O : Finset Nat) (a : Nat → Weight h)
    (mu : Measure (UnitSphere d)) (v : UnitSphere d → Weight d)
    (hv : ∀ w, inner Real w.val (v w) = 0) (hc : Continuous v) (z : Weight d) :
    meanFeatureJetAlongRetractFirst k O a mu v hv z 0 = meanFeatureJetAlongExpFirst k O a mu v hv z 0 ∧
    meanFeatureJetAlongRetractSecond k O a mu v hv z 0 = meanFeatureJetAlongExpSecond k O a mu v hv z 0 :=
  (meanFeatureJetAlongRetract_initial_jets k O a mu v hv hc z).2
example {d h : Nat} (k : Nat) (O : Finset Nat) (a : Nat → Weight h)
    (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] (v : UnitSphere d → Weight d)
    (hv : ∀ w, inner Real w.val (v w) = 0) (hc : Continuous v) (t : Real) :
    Integrable (fun z => norm (meanFeatureJetAlongRetractSecond k O a mu v hv z t)^2)
      (stdGaussian (Weight d)) :=
  (meanFeatureAlongRetract_gaussian_pow_integrable k O a mu v hv hc t 2).2.2

-- Gaussian exchange occurs before comparing the ordinary fit derivatives;
-- the full losses, with arbitrary original cap measures, agree to second order.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (P : SphericalVariation d)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    deriv (variationRetractedFitting O a P teacher1 teacher2) 0 =
      deriv (variationFitting O a P teacher1 teacher2) 0 ∧
    deriv (deriv (variationRetractedFitting O a P teacher1 teacher2)) 0 =
      deriv (deriv (variationFitting O a P teacher1 teacher2)) 0 :=
  variationRetractedFitting_derivatives_eq_exp O a P teacher1 teacher2
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (P : SphericalVariation d)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    (fun t => variationRetractedFitting O a P teacher1 teacher2 t -
      variationFitting O a P teacher1 teacher2 t) =o[𝓝 (0 : Real)] (fun t => t^2) :=
  variationRetractedFitting_sub_exp_littleO O a P teacher1 teacher2

-- An empty active block contributes no Gaussian fitting loss.
example {d h : Nat} (a : Nat → Weight h) (P : SphericalVariation d)
    (teacher1 teacher2 : Measure (UnitSphere d)) (t : Real) :
    variationRetractedFitting ∅ a P teacher1 teacher2 t = 0 := by
  simp [variationRetractedFitting, modelFitting, fittingEnergy, finiteHermiteActivation,
    meanFeature, outer]

-- General original-measure transport retains both factors of two.
example {d : Nat} (P : SphericalVariation d) :
    HasDerivAt (variationRetractedTransport P) (2*variationFirst P) 0 :=
  (variationRetractedTransport_variations P).1
example {d : Nat} (P : SphericalVariation d) :
    HasDerivAt (deriv (variationRetractedTransport P)) (2*variationSecond P) 0 :=
  (variationRetractedTransport_variations P).2.1

-- The zero-target case permits unequal atom speeds and noninteger p.
example {d : Nat} (P : SphericalVariation d) (lambda : Real)
    (hZ : variationTransport P 0 = 0) :
    HasDerivAt (deriv (variationRetractedRegularizer P lambda (5/2))) 0 0 :=
  (metricRegularizer_retracted_zero_variations P lambda (5/2) (by norm_num) hZ).2
example {d : Nat} (P : SphericalVariation d) (lambda : Real)
    (hZ : variationTransport P 0 = 0) :
    variationRetractedRegularizer P lambda (5/2) =o[𝓝 (0 : Real)] (fun t => t^2) :=
  metricRegularizer_retracted_zero_littleO P lambda (5/2) (by norm_num) hZ

-- Positive target distance uses the source p-2 coefficient, also at p=5/2.
example {d : Nat} (P : SphericalVariation d) (lambda p : Real) (hp : 2 < p)
    (hZ : 0 < variationTransport P 0) :
    HasDerivAt (deriv (variationRetractedRegularizer P lambda p))
      (lambda*(variationTransport P 0)^(p/2-1)*variationSecond P +
        lambda*(p-2)*(variationTransport P 0)^(p/2-2)*(variationFirst P)^2) 0 :=
  (metricRegularizer_retracted_positive_variations P lambda p hp hZ).2

-- The complete objective comparison is after every integral exchange.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (P : SphericalVariation d)
    (lambda p : Real) (hlambda : 0 < lambda) (hp : 2 < p)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    (fun t => variationRetractedObjective O a P lambda p teacher1 teacher2 t -
      variationObjective O a P lambda p teacher1 teacher2 t) =o[𝓝 (0 : Real)] (fun t => t^2) :=
  variationRetractedObjective_sub_exp_littleO O a P lambda p hlambda hp teacher1 teacher2
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (P : SphericalVariation d)
    (lambda p : Real) (hlambda : 0 < lambda) (hp : 2 < p)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    deriv (deriv (variationRetractedObjective O a P lambda p teacher1 teacher2)) 0 =
      deriv (deriv (variationObjective O a P lambda p teacher1 teacher2)) 0 :=
  (variationRetractedObjective_derivatives_eq_exp O a P lambda p hlambda hp teacher1 teacher2).2
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (P : SphericalVariation d)
    (lambda p : Real) (hlambda : 0 < lambda) (hp : 2 < p)
    (hZ : 0 < variationTransport P 0) (hE : 0 < variationEnergy P) :
    0 < deriv (deriv (variationRetractedObjective O a P lambda p (P.measure 0) (P.measure 1))) 0 :=
  normalized_objective_teacher_second_pos O a P lambda p hlambda hp hZ hE


-- Fractional exponents require only continuity of the vanishing power factor;
-- no derivative of Z^(p/2-1) is assumed at Z=0.
example {d : Nat} (P : SphericalVariation d) (lambda : Real)
    (hZ : variationTransport P 0 = 0) :
    HasDerivAt (variationRetractedRegularizer P lambda (5/2)) 0 0 ∧
    HasDerivAt (deriv (variationRetractedRegularizer P lambda (5/2))) 0 0 :=
  metricRegularizer_retracted_zero_variations P lambda (5/2) (by norm_num) hZ
example {d : Nat} (P : SphericalVariation d) (lambda : Real)
    (hZ : variationTransport P 0 = 0) :
    variationRetractedRegularizer P lambda (5/2) =o[𝓝 (0 : Real)] (fun t => t^2) :=
  metricRegularizer_retracted_zero_littleO P lambda (5/2) (by norm_num) hZ
example {d : Nat} (P : SphericalVariation d) (lambda : Real) :
    ∀ᶠ t in 𝓝 (0 : Real), DifferentiableAt Real
      (variationRetractedRegularizer P lambda (5/2)) t :=
  variationRetractedRegularizer_differentiable_near P lambda (5/2) (by norm_num)

-- Positive-distance coercivity retains the original spherical Hessian weight.
example {d : Nat} (P : SphericalVariation d) (lambda p : Real)
    (hlambda : 0 < lambda) (hp : 2 < p) (hZ : 0 < variationTransport P 0) :
    lambda*(variationTransport P 0)^(p/2-1)*sphericalRadialWeight P.radius*variationEnergy P ≤
      deriv (deriv (variationRetractedRegularizer P lambda p)) 0 :=
  metricRegularizer_retracted_second_lower_bound P lambda p hlambda hp hZ
