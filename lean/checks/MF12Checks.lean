import PaperFormalization.MatrixFactorization.SphericalObjectiveGradientSymmetry
import PaperFormalization.MatrixFactorization.AntisymmetricRetractionPath
import PaperFormalization.MatrixFactorization.AntisymmetricFittingGradientBounds
import PaperFormalization.MatrixFactorization.SphericalObjectiveSymmetry
import PaperFormalization.MatrixFactorization.SphericalCapSymmetry

/-! Source checks for actual Gaussian forces, their first-variation meaning,
and reflection of the original transport plans and cap measures. -/
open MeasureTheory ProbabilityTheory Set Filter Asymptotics
open scoped Topology
open PaperFormalization.MatrixFactorization
set_option autoImplicit false

-- Tangency holds before and after Gaussian integration.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (mu1 mu2 teacher1 teacher2 : Measure (UnitSphere d)) (i : Fin 2)
    (w : UnitSphere d) (z : Weight d) :
    inner Real w.val (fittingGradientIntegrand O a mu1 mu2 teacher1 teacher2 i w z) = 0 :=
  fittingGradientIntegrand_tangent O a mu1 mu2 teacher1 teacher2 i w z
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (mu1 mu2 teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure mu1] [IsProbabilityMeasure mu2]
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2]
    (i : Fin 2) (w : UnitSphere d) :
    inner Real w.val (sphericalFittingGradient O a mu1 mu2 teacher1 teacher2 i w) = 0 :=
  sphericalFittingGradient_tangent O a mu1 mu2 teacher1 teacher2 i w

-- Empty activation and exact teacher matching have vanishing fitting force.
example {d h : Nat} (a : Nat → Weight h)
    (mu1 mu2 teacher1 teacher2 : Measure (UnitSphere d)) (i : Fin 2) (w : UnitSphere d) :
    sphericalFittingGradient ∅ a mu1 mu2 teacher1 teacher2 i w = 0 := by
  simp [sphericalFittingGradient, fittingGradientIntegrand, finiteHermiteActivationJet]
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (mu1 mu2 : Measure (UnitSphere d)) (i : Fin 2) (w : UnitSphere d) :
    sphericalFittingGradient O a mu1 mu2 mu1 mu2 i w = 0 := by
  simp [sphericalFittingGradient, fittingGradientIntegrand, fittingOutputGradient]

-- The exact force represents the actual normalized first variation after
-- both original-measure and Gaussian integral exchanges.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (P : SphericalVariation d)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    HasDerivAt (variationRetractedFitting O a P teacher1 teacher2)
      (∑ i : Fin 2, ∫ w, inner Real
        (sphericalFittingGradient O a (P.measure 0) (P.measure 1) teacher1 teacher2 i w)
        (P.velocity i w) ∂P.measure i) 0 :=
  normalized_fitting_gradient_variation O a P teacher1 teacher2

-- The reflected branch has the positive teacher term and its exact
-- square-completion coefficient one-half.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (hO : ∀ n ∈ O, Odd n) (mu teacher : Measure (UnitSphere d))
    [IsFiniteMeasure mu] (z : Weight d) :
    fittingOutputGradient O a mu (reflectedMeasure mu) teacher teacher 0 z =
      antisymmetricOutputForce O a mu teacher z :=
  fittingOutputGradient_antibranch_zero O a hO mu teacher z
example {h : Nat} (x b e : Weight h) :
    -(1/2 : Real)*(norm x^2+norm b^2)*norm e^2 ≤
      2*inner Real (norm x^2 • x+inner Real x b • b) (x+e) :=
  antibranch_force_square_completion x b e
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (mu teacher : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure teacher] (i : Fin 2) (w : UnitSphere d) :
    norm (sphericalFittingGradient O a mu (reflectedMeasure mu) teacher teacher i w) ≤
      fittingCurvatureConstant d O a*Real.sqrt
        (productAntipodalTransportSq pole mu (reflectedMeasure mu)) :=
  antisymmetric_sphericalFittingGradient_product_bound O a hO pole mu teacher i w
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (teacher1 teacher2 : Measure (UnitSphere d)) (i : Fin 2) (w : UnitSphere d) :
    sphericalFittingGradient O a (antipodalMeasure pole) (antipodalMeasure pole)
      teacher1 teacher2 i w = 0 :=
  sphericalFittingGradient_antipodal O a hO pole teacher1 teacher2 i w

-- Unequal teachers must be exchanged together; the odd reflection identity
-- additionally reflects the point and reverses the force sign.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (mu1 mu2 teacher1 teacher2 : Measure (UnitSphere d)) (i : Fin 2) (w : UnitSphere d) :
    sphericalFittingGradient O a mu2 mu1 teacher2 teacher1 i w =
      sphericalFittingGradient O a mu1 mu2 teacher1 teacher2 i.rev w :=
  sphericalFittingGradient_exchange O a mu1 mu2 teacher1 teacher2 i w
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (hO : ∀ n ∈ O, Odd n) (mu1 mu2 teacher : Measure (UnitSphere d))
    [IsFiniteMeasure mu1] [IsFiniteMeasure mu2] (i : Fin 2) (w : UnitSphere d) :
    sphericalFittingGradient O a (reflectedMeasure mu2) (reflectedMeasure mu1)
      teacher teacher i (reflect w) =
      -sphericalFittingGradient O a mu1 mu2 teacher teacher i.rev w :=
  sphericalFittingGradient_reflection_exchange O a hO mu1 mu2 teacher i w

-- Reflection is an isometry of the actual all-coupling transport infimum.
example {d : Nat} (mu nu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    sphericalWassersteinSq (reflectedMeasure mu) (reflectedMeasure nu) =
      sphericalWassersteinSq mu nu := sphericalWassersteinSq_reflected mu nu
example {d : Nat} (pole : UnitSphere d) (lambda : Real)
    (mu1 mu2 : Measure (UnitSphere d)) [IsProbabilityMeasure mu1] [IsProbabilityMeasure mu2] :
    metricRegularizer pole lambda (5/2) (reflectedMeasure mu2) (reflectedMeasure mu1) =
      metricRegularizer pole lambda (5/2) mu1 mu2 :=
  metricRegularizer_reflection_exchange pole lambda (5/2) mu1 mu2
example {d h : Nat} (a : Nat → Weight h) (pole : UnitSphere d) (lambda : Real)
    (mu1 mu2 teacher : Measure (UnitSphere d)) [IsProbabilityMeasure mu1] [IsProbabilityMeasure mu2] :
    modelObjective {3,7} a pole lambda (5/2) (reflectedMeasure mu2) (reflectedMeasure mu1) teacher teacher =
      modelObjective {3,7} a pole lambda (5/2) mu1 mu2 teacher teacher := by
  apply modelObjective_reflection_exchange
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl <;> decide

-- Closed support and half masses are transported with the original measures.
example {d : Nat} (pole : UnitSphere d) (r : Real) (mu : Measure (UnitSphere d))
    (hcap : TwoCapClass pole r mu) : TwoCapClass pole r (reflectedMeasure mu) := hcap.reflected
example {d : Nat} (mu : Measure (UnitSphere d)) (f : UnitSphere d → UnitSphere d)
    (hf : Measurable f) :
    (reflectedMeasure mu).map (fun w => reflect (f (reflect w))) = reflectedMeasure (mu.map f) :=
  reflectedMeasure_map_conjugate mu f hf

-- Radial energy is the true optimum, including atomic cap laws.
example {d : Nat} (pole : UnitSphere d) (r : Real) (mu : Measure (UnitSphere d))
    (hc : TwoCapClass pole r mu) :
    (∫ w, norm (assignedGradient pole w)^2 ∂mu) = sphericalWassersteinSq mu (antipodalMeasure pole) :=
  assignedGradient_energy pole r mu hc
example {d : Nat} (P : SphericalVariation d) (lambda p : Real) :
    (∑ i : Fin 2, ∫ w, norm (metricGradient P.pole lambda p (P.measure 0) (P.measure 1) w)^2 ∂P.measure i) =
      (lambda*(variationTransport P 0)^(p/2-1))^2*variationTransport P 0 :=
  metricGradient_energy P lambda p

-- The full field is tangent and has a genuine original-measure pairing.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (P : SphericalVariation d)
    (lambda p : Real) (t1 t2 : Measure (UnitSphere d))
    [IsProbabilityMeasure t1] [IsProbabilityMeasure t2] (i : Fin 2) :
    Integrable (fun w => inner Real
      (sphericalObjectiveGradient O a P.pole lambda p (P.measure 0) (P.measure 1) t1 t2 i w)
      (P.velocity i w)) (P.measure i) :=
  sphericalObjectiveGradient_pairing_integrable O a P lambda p t1 t2 i
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (pole w : UnitSphere d)
    (lambda p : Real) (m1 m2 t1 t2 : Measure (UnitSphere d))
    [IsProbabilityMeasure m1] [IsProbabilityMeasure m2] [IsProbabilityMeasure t1] [IsProbabilityMeasure t2]
    (i : Fin 2) :
    inner Real w.val (sphericalObjectiveGradient O a pole lambda p m1 m2 t1 t2 i w) = 0 :=
  sphericalObjectiveGradient_tangent O a pole lambda p m1 m2 t1 t2 i w
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (P : SphericalVariation d)
    (lambda : Real) (t1 t2 : Measure (UnitSphere d))
    [IsProbabilityMeasure t1] [IsProbabilityMeasure t2] :
    HasDerivAt (variationRetractedObjective O a P lambda (5/2) t1 t2)
      (∑ i : Fin 2, ∫ w, inner Real
        (sphericalObjectiveGradient O a P.pole lambda (5/2) (P.measure 0) (P.measure 1) t1 t2 i w)
        (P.velocity i w) ∂P.measure i) 0 :=
  normalized_objective_gradient_variation O a P lambda (5/2) (by norm_num) t1 t2

-- Zero penalty and the stationary antipodal center retain their actual meanings.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (pole w : UnitSphere d)
    (p : Real) (m1 m2 t1 t2 : Measure (UnitSphere d)) (i : Fin 2) :
    sphericalObjectiveGradient O a pole 0 p m1 m2 t1 t2 i w =
      sphericalFittingGradient O a m1 m2 t1 t2 i w := by
  simp [sphericalObjectiveGradient,metricGradient]
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n)
    (pole w : UnitSphere d) (lambda : Real) (t1 t2 : Measure (UnitSphere d)) (i : Fin 2) :
    sphericalObjectiveGradient O a pole lambda (5/2) (antipodalMeasure pole) (antipodalMeasure pole)
      t1 t2 i w = 0 :=
  sphericalObjectiveGradient_antipodal O a hO pole lambda (5/2) (by norm_num) t1 t2 i w

-- Reflection covariance uses source caps, not the false equatorial tie identity.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n)
    (pole : UnitSphere d) (lambda p r : Real) (hr : r < Real.pi/2)
    (m1 m2 teacher : Measure (UnitSphere d)) [IsProbabilityMeasure m1] [IsProbabilityMeasure m2]
    (i : Fin 2) (w : UnitSphere d) (hw : w ∈ sphericalCap pole r ∪ sphericalCap (reflect pole) r) :
    sphericalObjectiveGradient O a pole lambda p (reflectedMeasure m2) (reflectedMeasure m1)
      teacher teacher i (reflect w) = -sphericalObjectiveGradient O a pole lambda p m1 m2 teacher teacher i.rev w :=
  sphericalObjectiveGradient_reflection_exchange O a hO pole lambda p m1 m2 teacher r hr i w hw
