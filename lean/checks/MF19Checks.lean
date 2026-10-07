import PaperFormalization.MatrixFactorization.GeodesicGaussianPair
import PaperFormalization.MatrixFactorization.GaussianFeatureL4Transfer
import PaperFormalization.MatrixFactorization.SourceGaussianL4
import PaperFormalization.MatrixFactorization.GaussianMeanFourthBound
import PaperFormalization.MatrixFactorization.FiniteMeasureFourthMean
import PaperFormalization.MatrixFactorization.GaussianFourthHolder


/-! Gaussian-law and actual-jet boundary diagnostics. These concern the
original finite activation and actual EXP path, without an L2 replacement
for a fourth-moment norm or an independent-pair hypothesis. -/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

-- Orthogonal observations need not have unit length to be independent.
example {d : Nat} (u v : Weight d) (huv : inner Real u v = 0) :
    IndepFun (fun z => inner Real ((2 : Real) • u) z)
      (fun z => inner Real ((3 : Real) • v) z) (stdGaussian (Weight d)) := by
  apply stdGaussian_inner_indepFun
  simp only [real_inner_smul_left, inner_smul_right, huv, mul_zero]

-- The actual pair law holds at negative signed times as well.
example {d : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (hn : v ≠ 0) (s : Real) :
    (stdGaussian (Weight d)).map (fun z =>
      (inner Real (geodesicPoint w v hv (-s)).val z,
       inner Real (sphereExpVelocity w v (-s)) z / norm v)) =
      (gaussianReal 0 1).prod (gaussianReal 0 1) :=
  geodesic_gaussian_normalized_pair_law w v hv hn (-s)

-- At order zero, the first feature derivative uses the actual first activation jet.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (w : UnitSphere d) (v : Weight d) (hv : inner Real w.val v = 0)
    (hn : v ≠ 0) (z : Weight d) (t : Real) :
    sphericalFeatureFirst 0 O a w v hv z t = norm v •
      ((inner Real (sphereExpVelocity w v t) z / norm v) •
        finiteHermiteActivationJet 1 O a (inner Real (geodesicPoint w v hv t).val z)) :=
  sphericalFeatureFirst_gaussian_pair_factorization 0 O a w v hv hn z t

-- Stationary paths have both derivatives zero; this statement contains no division.
example {d h : Nat} (k : Nat) (O : Finset Nat) (a : Nat → Weight h)
    (w : UnitSphere d) (z : Weight d) (t : Real) :
    sphericalFeatureFirst k O a w 0 (by simp) z t = 0 ∧
      sphericalFeatureSecond k O a w 0 (by simp) z t = 0 :=
  sphericalFeature_derivatives_zero_velocity k O a w (by simp) z t

-- The exact second fourth-moment transfer keeps the radial subtraction inside the norm.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (u v : UnitSphere d) (huv : inner Real u.val v.val = 0) :
    (∫ z : Weight d, norm ((inner Real v.val z)^2 •
      finiteHermiteActivationJet 2 O a (inner Real u.val z) -
      inner Real u.val z • finiteHermiteActivationJet 1 O a (inner Real u.val z))^4
      ∂stdGaussian (Weight d)) =
      ∫ g : Real × Real, norm (g.2^2 • finiteHermiteActivationJet 2 O a g.1 -
        g.1 • finiteHermiteActivationJet 1 O a g.1)^4
        ∂(gaussianReal 0 1).prod (gaussianReal 0 1) :=
  finiteHermite_second_fourth_orthogonal_pair O a u v huv

-- The actual pair map is measurable even before excluding zero speed; its
-- independent standard law is claimed only under the separate nonzero premise.
example {d : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (t : Real) :
    Measurable (fun z : Weight d =>
      (inner Real (geodesicPoint w v hv t).val z,
        inner Real (sphereExpVelocity w v t) z / norm v)) := by
  fun_prop

end PaperFormalization.MatrixFactorization


/-! Boundary checks for the actual source fourth norms and spherical jets. -/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization.MF19L4Checks
open PaperFormalization.MatrixFactorization
set_option autoImplicit false

-- An empty activation has three genuinely zero fourth norms, including the combined second jet.
example {h : Nat} (a : Nat → Weight h) :
    gaussianActivationL4 ∅ a = 0 ∧ gaussianFirstJetL4 ∅ a = 0 ∧
      gaussianSecondJetL4 ∅ a = 0 := by
  have he : finiteHermiteActivation ∅ a = (fun _ : Real => (0 : Weight h)) := by
    funext x
    simp [finiteHermiteActivation]
  simp [gaussianActivationL4, gaussianFirstJetL4, gaussianSecondJetL4,
    he, finiteHermiteActivationJet]

-- Stationary actual paths have zero first and second jet norms without a normalized tangent.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (w : UnitSphere d) (hv : inner Real w.val (0 : Weight d) = 0) (t : Real) :
    lpNorm (fun z => sphericalFeatureFirst 0 O a w 0 hv z t) 4
      (stdGaussian (Weight d)) = 0 ∧
    lpNorm (fun z => sphericalFeatureSecond 0 O a w 0 hv z t) 4
      (stdGaussian (Weight d)) = 0 := by
  constructor
  · simpa using sphericalFeatureFirst_lpNorm_four O a w 0 hv t
  · simpa using sphericalFeatureSecond_lpNorm_four O a w 0 hv t

-- The exact source constants also apply at a negative signed time, with no cap assumption.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (w : UnitSphere d) (v : Weight d) (hv : inner Real w.val v = 0) (s : Real) :
    lpNorm (fun z => sphericalFeatureFirst 0 O a w v hv z (-s)) 4
      (stdGaussian (Weight d)) = norm v * gaussianFirstJetL4 O a ∧
    lpNorm (fun z => sphericalFeatureSecond 0 O a w v hv z (-s)) 4
      (stdGaussian (Weight d)) = norm v^2 * gaussianSecondJetL4 O a :=
  ⟨sphericalFeatureFirst_lpNorm_four O a w v hv (-s),
    sphericalFeatureSecond_lpNorm_four O a w v hv (-s)⟩

-- K2 is finite before passing to the real norm; its value does not rely on infinity mapping to zero.
example {h : Nat} (O : Finset Nat) (a : Nat → Weight h) :
    eLpNorm (fun xy : Real × Real =>
      xy.2^2 • finiteHermiteActivationJet 2 O a xy.1 -
        xy.1 • finiteHermiteActivationJet 1 O a xy.1)
      4 ((gaussianReal 0 1).prod (gaussianReal 0 1)) < ⊤ ∧
    ENNReal.ofReal (gaussianSecondJetL4 O a) =
      eLpNorm (fun xy : Real × Real =>
        xy.2^2 • finiteHermiteActivationJet 2 O a xy.1 -
          xy.1 • finiteHermiteActivationJet 1 O a xy.1)
        4 ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
  ⟨(gaussianPair_secondJet_memLp_four O a).2,
    ofReal_lpNorm (gaussianPair_secondJet_memLp_four O a)⟩

end PaperFormalization.MatrixFactorization.MF19L4Checks


/-! Boundary checks for original mean features and exact finite-mass averaging. -/
open MeasureTheory ProbabilityTheory Set Filter Function
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Every original teacher probability is covered, without an oddness or cap premise. -/
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    (∫ z : Weight d, norm (meanFeature (finiteHermiteActivation O a) teacher z)^4
      ∂stdGaussian (Weight d)) ≤
      ∫ g : Real, norm (finiteHermiteActivation O a g)^4 ∂gaussianReal 0 1 :=
  finiteHermite_mean_fourth_le_scalar O a teacher

/-- An empty active block has exactly zero fourth moment on both sides. -/
example {d h : Nat} (a : Nat → Weight h) (mu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] :
    (∫ z : Weight d, norm (meanFeature (finiteHermiteActivation ∅ a) mu z)^4
      ∂stdGaussian (Weight d)) = 0 ∧
      (∫ g : Real, norm (finiteHermiteActivation ∅ a g)^4 ∂gaussianReal 0 1) = 0 := by
  simp [meanFeature,finiteHermiteActivation]

/-- The mean estimate applies in ambient dimension one; it uses no transverse pair. -/
example {h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (mu : Measure (UnitSphere 1)) [IsProbabilityMeasure mu] :
    (∫ z : Weight 1, norm (meanFeature (finiteHermiteActivation O a) mu z)^4
      ∂stdGaussian (Weight 1)) ≤
      ∫ g : Real, norm (finiteHermiteActivation O a g)^4 ∂gaussianReal 0 1 :=
  finiteHermite_mean_fourth_le_scalar O a mu

/-- At an actual Dirac weight the scalar Gaussian moment is attained exactly. -/
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (w : UnitSphere d) :
    (∫ z : Weight d, norm (meanFeature (finiteHermiteActivation O a) (Measure.dirac w) z)^4
      ∂stdGaussian (Weight d)) =
      ∫ g : Real, norm (finiteHermiteActivation O a g)^4 ∂gaussianReal 0 1 := by
  simp only [meanFeature,integral_dirac]
  rw [← stdGaussian_map_inner_unit w]
  symm
  exact integral_map (by fun_prop)
    (((finiteHermiteActivation_continuous O a).norm.pow 4).aestronglyMeasurable)

/-- Zero total mass is included, without a nonzero-measure instance. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    (F : Real → E) :
    norm (∫ w, F w ∂(0 : Measure Real))^4 ≤
      ((0 : Measure Real).real univ)^3*(∫ w, norm (F w)^4 ∂(0 : Measure Real)) := by
  apply finiteMeasure_norm_integral_fourth_le
  · simp
  · simp

/-- A mass-two measure is not a probability: the exact cubic factor is necessary. -/
example (x : Real) :
    norm (∫ _w : Real, x ∂((2 : ENNReal) • Measure.dirac 0))^4 =
      (((2 : ENNReal) • Measure.dirac (0 : Real)).real univ)^3 *
        (∫ _w : Real, norm x^4 ∂((2 : ENNReal) • Measure.dirac 0)) := by
  simp [Measure.real,norm_mul,mul_pow]
  ring

end PaperFormalization.MatrixFactorization


/-! Fourth-norm product diagnostics retain genuine integrability assumptions
for the remaining factors. No probability normalization is used. -/
open MeasureTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

-- A zero vector-valued factor gives an integrable zero product and the exact
-- zero upper bound, while the three other factors remain arbitrary L4 functions.
example {α E F G H : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedAddCommGroup G] [NormedAddCommGroup H]
    {mu : Measure α} {g : α → F} {h : α → G} {k : α → H}
    (hg : MemLp g 4 mu) (hh : MemLp h 4 mu) (hk : MemLp k 4 mu) :
    Integrable (fun x => norm (0 : E)*norm (g x)*norm (h x)*norm (k x)) mu ∧
      (∫ x, norm (0 : E)*norm (g x)*norm (h x)*norm (k x) ∂mu) ≤ 0 := by
  simpa only [norm_zero,zero_mul,lpNorm_fun_zero] using
    four_norm_integrable_and_le (MemLp.zero' : MemLp (fun _ : α => (0 : E)) 4 mu) hg hh hk

-- A finite measure need not be a probability measure for the squared-factor
-- product to be integrable and satisfy the same exact L4 bound.
example {α E F G : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    {mu : Measure α} [IsFiniteMeasure mu]
    {f : α → E} {g : α → F} {h : α → G}
    (hf : MemLp f 4 mu) (hg : MemLp g 4 mu) (hh : MemLp h 4 mu) :
    Integrable (fun x => norm (f x)^2*norm (g x)*norm (h x)) mu ∧
      (∫ x, norm (f x)^2*norm (g x)*norm (h x) ∂mu) ≤
        lpNorm f 4 mu^2*lpNorm g 4 mu*lpNorm h 4 mu := by
  constructor
  · simpa only [pow_two] using (four_norm_integrable_and_le hf hf hg hh).1
  · exact integral_norm_sq_mul_norm_mul_norm_le_lpNorm_four hf hg hh

end PaperFormalization.MatrixFactorization
