import PaperFormalization.MatrixFactorization.GaussianActiveQuartic
import PaperFormalization.MatrixFactorization.FittingEnergy

/-! # MF38: an actual quartic fitting polynomial on the source Hilbert space

The four-linear coefficients are the genuine Gaussian integrals from the
previous module. The formula below is proved equal to the original fitting
energy after the original raw moments are substituted. It does not assume
that equality or identify the separate chaos-contraction coefficient formula.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

noncomputable def activeFittingPolynomial {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (teacher : ActiveMomentSpace d O) (X : ActiveMomentCoordinates d O) : Real :=
  (1 / 2 : Real) *
    (activeGaussianQuartic O a ![X 0 + X 1, X 0 - X 1, X 0 + X 1, X 0 - X 1] -
     2 * activeGaussianQuartic O a ![X 0 + X 1, X 0 - X 1, teacher, teacher] +
     activeGaussianQuartic O a ![teacher, teacher, teacher, teacher])

/-- The fourth-, second-, and zeroth-degree terms form a smooth actual polynomial. -/
theorem activeFittingPolynomial_contDiff {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (teacher : ActiveMomentSpace d O) :
    ContDiff Real ⊤ (activeFittingPolynomial O a teacher) := by
  unfold activeFittingPolynomial
  letI : NormedSpace Real (ActiveMomentCoordinates d O) := PiLp.normedSpace 2 Real _
  letI : NormedSpace Real (Fin 4 → ActiveMomentSpace d O) := Pi.normedSpace
  have hp : ContDiff Real ⊤ (fun X : ActiveMomentCoordinates d O => X 0 + X 1) :=
    (PiLp.proj (𝕜 := Real) 2 (fun _ : Fin 2 => ActiveMomentSpace d O) 0).contDiff.add
      (PiLp.proj (𝕜 := Real) 2 (fun _ : Fin 2 => ActiveMomentSpace d O) 1).contDiff
  have hm : ContDiff Real ⊤ (fun X : ActiveMomentCoordinates d O => X 0 - X 1) :=
    (PiLp.proj (𝕜 := Real) 2 (fun _ : Fin 2 => ActiveMomentSpace d O) 0).contDiff.sub
      (PiLp.proj (𝕜 := Real) 2 (fun _ : Fin 2 => ActiveMomentSpace d O) 1).contDiff
  have h4 : ContDiff Real ⊤ (fun X : ActiveMomentCoordinates d O =>
      (![X 0 + X 1, X 0 - X 1, X 0 + X 1, X 0 - X 1] : Fin 4 → ActiveMomentSpace d O)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> first | exact hp | exact hm
  have h2 : ContDiff Real ⊤ (fun X : ActiveMomentCoordinates d O =>
      (![X 0 + X 1, X 0 - X 1, teacher, teacher] : Fin 4 → ActiveMomentSpace d O)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> first | exact hp | exact hm | exact contDiff_const
  have hQ : ContDiff Real ⊤ (fun v : Fin 4 → ActiveMomentSpace d O => activeGaussianQuartic O a v) :=
    ContinuousMultilinearMap.contDiff (𝕜 := Real) (F := Real)
      (E := fun _ : Fin 4 => ActiveMomentSpace d O) (activeGaussianQuartic O a)
  have hc : ContDiff Real ⊤ (fun _ : ActiveMomentCoordinates d O =>
      activeGaussianQuartic O a ![teacher, teacher, teacher, teacher]) := contDiff_const
  have hc2 : ContDiff Real ⊤ (fun _ : ActiveMomentCoordinates d O => (2 : Real)) := contDiff_const
  have hcHalf : ContDiff Real ⊤ (fun _ : ActiveMomentCoordinates d O => (1 / 2 : Real)) := contDiff_const
  exact hcHalf.mul (((hQ.comp h4).sub (hc2.mul (hQ.comp h2))).add hc)

/-- The polynomial is exactly the Gaussian matrix residual, on arbitrary active inputs. -/
theorem activeFittingPolynomial_eq_fittingEnergy {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (teacher : ActiveMomentSpace d O) (X : ActiveMomentCoordinates d O) :
    activeFittingPolynomial O a teacher X =
      fittingEnergy (stdGaussian (Weight d))
        (fun z => outer (activeHermiteFeature O a z teacher) (activeHermiteFeature O a z teacher))
        (fun z => activeHermiteFeature O a z (X 0 + X 1))
        (fun z => activeHermiteFeature O a z (X 0 - X 1)) := by
  let f4 := fun z : Weight d =>
    inner Real (activeHermiteFeature O a z (X 0 + X 1)) (activeHermiteFeature O a z (X 0 + X 1)) *
    inner Real (activeHermiteFeature O a z (X 0 - X 1)) (activeHermiteFeature O a z (X 0 - X 1))
  let f2 := fun z : Weight d =>
    inner Real (activeHermiteFeature O a z (X 0 + X 1)) (activeHermiteFeature O a z teacher) *
    inner Real (activeHermiteFeature O a z (X 0 - X 1)) (activeHermiteFeature O a z teacher)
  let f0 := fun z : Weight d =>
    inner Real (activeHermiteFeature O a z teacher) (activeHermiteFeature O a z teacher) *
    inner Real (activeHermiteFeature O a z teacher) (activeHermiteFeature O a z teacher)
  have hi4 : Integrable f4 (stdGaussian (Weight d)) :=
    activeQuartic_scalar_integrable O a ![X 0 + X 1, X 0 - X 1, X 0 + X 1, X 0 - X 1]
  have hi2 : Integrable f2 (stdGaussian (Weight d)) :=
    activeQuartic_scalar_integrable O a ![X 0 + X 1, X 0 - X 1, teacher, teacher]
  have hi0 : Integrable f0 (stdGaussian (Weight d)) :=
    activeQuartic_scalar_integrable O a ![teacher, teacher, teacher, teacher]
  have he (z : Weight d) :
      ‖outer (activeHermiteFeature O a z (X 0 + X 1)) (activeHermiteFeature O a z (X 0 - X 1)) -
        outer (activeHermiteFeature O a z teacher) (activeHermiteFeature O a z teacher)‖ ^ 2 =
      f4 z - 2 * f2 z + f0 z := by
    simp only [norm_sub_sq_real, outer_norm_sq, outer_inner, f4, f2, f0, real_inner_self_eq_norm_sq]
  unfold activeFittingPolynomial fittingEnergy
  simp only [activeGaussianQuartic_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_succ]
  change (1 / 2 : Real) * ((∫ z, f4 z ∂stdGaussian (Weight d)) -
    2 * (∫ z, f2 z ∂stdGaussian (Weight d)) + (∫ z, f0 z ∂stdGaussian (Weight d))) = _
  simp_rw [he]
  rw [integral_add (f := fun z => f4 z - 2 * f2 z) (g := f0)
      (hi4.sub (hi2.const_mul 2)) hi0,
    integral_sub (f := f4) (g := fun z => 2 * f2 z) hi4 (hi2.const_mul 2), integral_const_mul]

/-- The squared matrix residual is genuinely integrable on every active input. -/
theorem activeFittingPolynomial_residual_integrable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (teacher : ActiveMomentSpace d O) (X : ActiveMomentCoordinates d O) :
    Integrable (fun z : Weight d =>
      ‖outer (activeHermiteFeature O a z (X 0 + X 1)) (activeHermiteFeature O a z (X 0 - X 1)) -
        outer (activeHermiteFeature O a z teacher) (activeHermiteFeature O a z teacher)‖ ^ 2)
      (stdGaussian (Weight d)) := by
  have hs (Y : ActiveMomentSpace d O) :=
    (activeHermiteFeature_contDiff_input O a Y).continuous.measurable.stronglyMeasurable
  have hp (Y : ActiveMomentSpace d O) := activeHermiteFeature_power_integrable O a Y 4
  exact fittingEnergy_integrable _ _ _ _
    (outer_stronglyMeasurable _ _ (hs teacher) (hs teacher))
    (hs (X 0 + X 1)) (hs (X 0 - X 1))
    (outer_sq_integrable _ _ _ (hs teacher) (hs teacher) (hp teacher) (hp teacher))
    (hp (X 0 + X 1)) (hp (X 0 - X 1))

/-- Nonnegativity is inherited from the proved actual squared-residual identity. -/
theorem activeFittingPolynomial_nonneg {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (teacher : ActiveMomentSpace d O) (X : ActiveMomentCoordinates d O) :
    0 ≤ activeFittingPolynomial O a teacher X := by
  rw [activeFittingPolynomial_eq_fittingEnergy]
  exact fittingEnergy_nonneg _ _ _ _

/-- The original sphere model supplies its actual teacher and both actual student features. -/
theorem activeFittingPolynomial_original_measures {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (teacher mu nu : Measure (UnitSphere d))
    [IsFiniteMeasure teacher] [IsFiniteMeasure mu] [IsFiniteMeasure nu] :
    activeFittingPolynomial O a (rawActiveMoment O teacher) (activeMomentMap O mu nu) =
      fittingEnergy (stdGaussian (Weight d))
        (fun z => outer (meanFeature (finiteHermiteActivation O a) teacher z)
          (meanFeature (finiteHermiteActivation O a) teacher z))
        (meanFeature (finiteHermiteActivation O a) mu)
        (meanFeature (finiteHermiteActivation O a) nu) := by
  rw [activeFittingPolynomial_eq_fittingEnergy]
  simp only [activeHermiteFeature_rawMoment, activeHermiteFeature_left, activeHermiteFeature_right]

end PaperFormalization.MatrixFactorization
