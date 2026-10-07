import PaperFormalization.MatrixFactorization.SphericalCharacteristicFittingEnergy
import PaperFormalization.MatrixFactorization.SphericalCharacteristicPersistence
import PaperFormalization.MatrixFactorization.AntisymmetricGradientEnergy

/-! # MF15: full objective energy dissipation on actual characteristics

The function differentiated here is the original
Gaussian fitting energy plus the true angular-transport regularizer. The
transport derivative and both fitting derivative exchanges have already been
derived. Genuine pairing and squared-gradient integrability are retained.
The equality needs no branch assumption. A quantitative negative upper bound
then uses the initial-only mean-distance persistence on a GIVEN cap interval.
Neither global cap confinement nor the printed sharp initial basin is claimed.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}

noncomputable def SphericalCharacteristicSolution.objective
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (t : Real) : Real := modelObjective O a pole lambda p
      (X.measure 0 t) (X.measure 1 t) teacher teacher

noncomputable def SphericalCharacteristicSolution.gradientEnergy
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (t : Real) : Real := ∑ i : Fin 2, ∫ w,
      norm (sphericalObjectiveGradient O a pole lambda p (X.measure 0 t) (X.measure 1 t)
        teacher teacher i w)^2 ∂X.measure i t

theorem SphericalCharacteristicSolution.gradientEnergy_integrable
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (i : Fin 2) (t : Real) (ht : t ∈ Icc 0 T) :
    Integrable (fun w => norm (sphericalObjectiveGradient O a pole lambda p
      (X.measure 0 t) (X.measure 1 t) teacher teacher i w)^2) (X.measure i t) :=
  sphericalObjectiveGradient_norm_sq_integrable O a pole radius lambda p
    (fun j => X.measure j t) (fun j => X.cap j t ht) teacher teacher i

theorem SphericalCharacteristicSolution.gradientEnergy_nonneg
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (t : Real) : 0 ≤ X.gradientEnergy t :=
  Finset.sum_nonneg (fun i _ => integral_nonneg (fun w => sq_nonneg _))

/-- Both the metric pairing and its value are obtained under the actual law. -/
theorem SphericalCharacteristicSolution.metric_velocity_pairing
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (i : Fin 2) (t : Real) (ht : t ∈ Icc 0 T) :
    Integrable (fun w => inner Real (metricGradient pole lambda p (X.measure 0 t) (X.measure 1 t) w)
      (X.velocity i t w)) (X.measure i t) ∧
    (∫ w, inner Real (metricGradient pole lambda p (X.measure 0 t) (X.measure 1 t) w)
      (X.velocity i t w) ∂X.measure i t) =
      -lambda*(X.transport t)^(p/2-1) *
        (∫ w, inner Real (sphericalObjectiveGradient O a pole lambda p
          (X.measure 0 t) (X.measure 1 t) teacher teacher i w)
          (assignedGradient pole w) ∂X.measure i t) := by
  have hi := objective_radial_pairing_integrable O a pole radius lambda p
    (fun j => X.measure j t) (fun j => X.cap j t ht) teacher teacher i
  have he : (fun w => inner Real (metricGradient pole lambda p (X.measure 0 t) (X.measure 1 t) w)
      (X.velocity i t w)) =
      (fun w => (-lambda*(X.transport t)^(p/2-1))*inner Real
        (sphericalObjectiveGradient O a pole lambda p (X.measure 0 t) (X.measure 1 t) teacher teacher i w)
        (assignedGradient pole w)) := by
    funext w
    simp only [metricGradient,SphericalCharacteristicSolution.velocity,
      SphericalCharacteristicSolution.transport,real_inner_smul_left,inner_neg_right]
    rw [real_inner_comm (assignedGradient pole w)]
    ring
  rw [he]
  exact ⟨hi.const_mul _,integral_const_mul _ _⟩

/-- Chain rule for the true regularizer, including zero transport for p>2. -/
theorem SphericalCharacteristicSolution.regularizer_hasDerivAt
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hp : 2 < p) (t : Real) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun s => metricRegularizer pole lambda p (X.measure 0 s) (X.measure 1 s))
      (∑ i : Fin 2, ∫ w,
        inner Real (metricGradient pole lambda p (X.measure 0 t) (X.measure 1 t) w)
          (X.velocity i t w) ∂X.measure i t) t := by
  have hz := X.productTransport_hasDerivAt hp t ht
  have hd := (hz.rpow_const (p := p/2) (Or.inr (by linarith))).const_mul (lambda/p)
  have hpair (i : Fin 2) := (X.metric_velocity_pairing i t ⟨ht.1.le,ht.2.le⟩).2
  apply hd.congr_deriv
  simp_rw [hpair]
  rw [← Finset.mul_sum]
  dsimp only [SphericalCharacteristicSolution.transport]
  have hp0 : p ≠ 0 := by linarith
  field_simp [hp0]

/-- Exact full energy dissipation. The source ODE is only needed on the
original conull support. No derivative is asserted at either time endpoint. -/
theorem SphericalCharacteristicSolution.objective_hasDerivAt
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hp : 2 < p) (t : Real) (ht : t ∈ Ioo 0 T) :
    HasDerivAt X.objective (-X.gradientEnergy t) t := by
  have htc : t ∈ Icc (0 : Real) T := ⟨ht.1.le,ht.2.le⟩
  letI : IsProbabilityMeasure (X.measure 0 t) := (X.cap 0 t htc).probability
  letI : IsProbabilityMeasure (X.measure 1 t) := (X.cap 1 t htc).probability
  have hfit (i : Fin 2) : Integrable (fun w => inner Real
      (sphericalFittingGradient O a (X.measure 0 t) (X.measure 1 t) teacher teacher i w)
      (X.velocity i t w)) (X.measure i t) := by
    letI : IsProbabilityMeasure (X.measure i t) := (X.cap i t htc).probability
    exact (fitting_measurable_velocity_pairing O a (X.measure 0 t) (X.measure 1 t)
      teacher teacher (X.measure i t) i (X.velocity i t) (X.velocity_measurable i t htc)
      (X.velocity_norm_integrable hp i t htc)
      (Eventually.of_forall (X.velocity_tangent i t htc))).1
  have hmetric := fun i => (X.metric_velocity_pairing i t htc).1
  have hd := (X.fitting_hasDerivAt hp t ht).add (X.regularizer_hasDerivAt hp t ht)
  apply hd.congr_deriv
  rw [← Finset.sum_add_distrib]
  have he (i : Fin 2) :
      (∫ w, inner Real (sphericalFittingGradient O a (X.measure 0 t) (X.measure 1 t) teacher teacher i w)
        (X.velocity i t w) ∂X.measure i t) +
      (∫ w, inner Real (metricGradient pole lambda p (X.measure 0 t) (X.measure 1 t) w)
        (X.velocity i t w) ∂X.measure i t) =
      -(∫ w, norm (sphericalObjectiveGradient O a pole lambda p
        (X.measure 0 t) (X.measure 1 t) teacher teacher i w)^2 ∂X.measure i t) := by
    rw [← integral_add (hfit i) (hmetric i),← integral_neg]
    apply integral_congr_ae
    filter_upwards with w
    rw [← inner_add_left]
    change inner Real (sphericalObjectiveGradient O a pole lambda p
      (X.measure 0 t) (X.measure 1 t) teacher teacher i w)
      (-sphericalObjectiveGradient O a pole lambda p
        (X.measure 0 t) (X.measure 1 t) teacher teacher i w) = _
    rw [inner_neg_right,real_inner_self_eq_norm_sq]
  simp_rw [he]
  simp only [Finset.sum_neg_distrib,SphericalCharacteristicSolution.gradientEnergy]

/-- Closed-time energy continuity comes from actual feature and transport
continuity, not from an assumed abstract Wasserstein chain rule. -/
theorem SphericalCharacteristicSolution.objective_continuousOn
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hp : 2 < p) :
    ContinuousOn X.objective (Icc 0 T) := by
  have hm : ContinuousOn (fun t => metricRegularizer pole lambda p
      (X.measure 0 t) (X.measure 1 t)) (Icc 0 T) :=
    (X.productTransport_continuousOn.rpow_const (fun t ht => Or.inr (by linarith))).const_mul (lambda/p)
  exact X.fitting_continuousOn.add hm

theorem SphericalCharacteristicSolution.objective_antitoneOn
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hp : 2 < p) : AntitoneOn X.objective (Icc 0 T) := by
  apply scalar_antitone_on_closed_interval (X.objective_continuousOn hp)
    (fun t ht => (X.objective_hasDerivAt hp t ht).differentiableAt)
  intro t ht
  rw [(X.objective_hasDerivAt hp t ht).deriv]
  exact neg_nonpos.mpr (X.gradientEnergy_nonneg t)

/-- Quantitative energy decay uses the initial-only transport persistence,
not a smallness hypothesis imposed again at the evaluation time. -/
theorem SphericalCharacteristicSolution.objective_deriv_le_from_initial
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0))
    (hl : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (hsmall0 : productAntipodalTransportSq pole (initial 0) (initial 1) ≤
      coarseRadialRadius lambda p (fittingCurvatureConstant d O a/64))
    (t : Real) (ht : t ∈ Ioo 0 T) :
    deriv X.objective t ≤ -(lambda^2/4)*(X.transport t)^(p-1) := by
  have htc : t ∈ Icc (0 : Real) T := ⟨ht.1.le,ht.2.le⟩
  have hb := spherical_characteristic_antibranch_invariant hO X hunique hinitial t htc
  have hs := (X.transport_persists hO hunique hinitial hl hp hp4 hsmall0).2 t htc
  have hs' : productAntipodalTransportSq pole (X.measure 0 t) (reflectedMeasure (X.measure 0 t)) ≤
      coarseRadialRadius lambda p (fittingCurvatureConstant d O a/64) := by
    simpa only [SphericalCharacteristicSolution.transport,hb] using hs.2.2
  have hg := antisymmetricGradientEnergy_lower O a hO pole radius lambda p hl hp hp4
    (X.measure 0 t) (X.cap 0 t htc) teacher hs'
  rw [(X.objective_hasDerivAt hp t ht).deriv]
  simpa only [SphericalCharacteristicSolution.gradientEnergy,SphericalCharacteristicSolution.transport,
    Fin.sum_univ_two,hb,antisymmetricGradientEnergy,neg_mul] using neg_le_neg hg

theorem SphericalCharacteristicSolution.objective_deriv_negative_from_initial
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0))
    (hl : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (hsmall0 : productAntipodalTransportSq pole (initial 0) (initial 1) ≤
      coarseRadialRadius lambda p (fittingCurvatureConstant d O a/64))
    (t : Real) (ht : t ∈ Ioo 0 T) (hz : 0 < X.transport t) : deriv X.objective t < 0 :=
  (X.objective_deriv_le_from_initial hO hunique hinitial hl hp hp4 hsmall0 t ht).trans_lt
    (mul_neg_of_neg_of_pos (by nlinarith [sq_pos_of_pos hl]) (Real.rpow_pos_of_pos hz _))

end PaperFormalization.MatrixFactorization
