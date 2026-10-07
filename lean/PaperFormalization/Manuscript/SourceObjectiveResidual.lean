import PaperFormalization.Manuscript.SourceActualGramRegularity
import PaperFormalization.Manuscript.SourceEmpiricalPopulationField
import PaperFormalization.Manuscript.FeatureDisplacement
import PaperFormalization.Manuscript.SourceUniformGammaComplete

/-! # The actual objective discrepancy on the source population/radius event

M13t verified implementation. The objective is the original G of the actual
Bochner moment, and the empirical measure uses exactly 1/N. This statement
includes genuine feature integrability. Its proof never divides by L and
never assumes a scalar objective or feature-displacement estimate.
-/
open MeasureTheory Set
open scoped NNReal BigOperators
namespace PaperFormalization.Manuscript
variable {N d : Nat}
variable {H : Nat -> Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace Real (H n)] [∀ n, CompleteSpace (H n)]
set_option maxSynthPendingDepth 10 in
set_option maxHeartbeats 2400000 in
/-- The fixed-time functional-gap lemma, with the literal Lambda and Gamma.
The population measure keeps the original all-real-order moment class. -/
theorem source_objective_gap_le_discrepancy_and_residual
    (c C g p q K D alpha C3 : Real) (phi : ∀ n, EuclideanSpace Real (Fin d) -> H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (hK : 0 < K) (hD : 1 ≤ D)
    (hphi : ∀ n, ContDiff Real 2 (phi n))
    (hgrowth : ∀ n z k, k ≤ 2 -> norm (iteratedFDeriv Real k (phi n) z) ≤
      featureGrowth C g q n * (1 + norm z ^ (n+1-k)))
    (G : lp H 2 -> Real) (U : Set (lp H 2)) (hU : IsOpen U)
    (hSU : measureMomentRegion (sourceWeightedFeatureMap c p phi) (sourceMomentClass alpha K) D ⊆ U)
    (hG : ContDiffOn Real 3 G U)
    (hthirdG : ∀ theta, theta ∈ measureMomentRegion (sourceWeightedFeatureMap c p phi)
      (sourceMomentClass alpha K) D -> norm (iteratedFDeriv Real 3 G theta) ≤ C3)
    (L : NNReal) (hL : (L : Real) = sourceComparisonEnvelope c C g p q K D alpha C3 phi G)
    (mu : Measure (EuclideanSpace Real (Fin d))) (hmu : mu ∈ sourceMomentClass alpha K)
    (X Y : PiLp 2 (fun _ : Fin N => EuclideanSpace Real (Fin d)))
    (hN : 0 < N) (hX : ∀ i, norm (X i) ≤ D) (hY : ∀ i, norm (Y i) ≤ D) :
    Integrable (sourceWeightedFeatureMap c p phi) mu ∧
      norm (G (empiricalMomentMap (sourceWeightedFeatureMap c p phi) X) -
        G (∫ z, sourceWeightedFeatureMap c p phi z ∂mu)) ≤
      featureDisplacementLambda c C g p q D L * (norm (X-Y) / Real.sqrt N) +
        weightedSampleResidual (featureResidualWeight c p L) phi
          (fun n => ∫ z, phi n z ∂mu) (fun i => Y i) := by
  classical
  letI : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  letI : IsProbabilityMeasure mu := sourceMomentClass_isProbabilityMeasure alpha K mu hmu
  have hvalue : ∀ n z, norm (phi n z) ≤ featureGrowth C g q n * (1+norm z^(n+1)) := by
    intro n z
    simpa only [norm_iteratedFDeriv_zero, Nat.sub_zero] using hgrowth n z 0 (by omega)
  have hdiff : ∀ n z, z ∈ Metric.closedBall (0 : EuclideanSpace Real (Fin d)) D ->
      DifferentiableAt Real (phi n) z := fun n z _ => (hphi n).differentiable (by norm_num) z
  have hderiv : ∀ n z, z ∈ Metric.closedBall (0 : EuclideanSpace Real (Fin d)) D ->
      norm (fderiv Real (phi n) z) ≤ featureGrowth C g q n * (1+norm z^n) := by
    intro n z _
    simpa only [norm_iteratedFDeriv_one, Nat.add_sub_cancel] using hgrowth n z 1 (by omega)
  have hpop : ∀ n, norm (∫ z, phi n z ∂mu) ≤ featureGrowth C g q n *
      (1+K^(n+1)*((n+1 : Nat) : Real)^(((n+1 : Nat) : Real)/alpha)) := by
    intro n
    exact norm_coordinate_feature_integral_le mu id (phi n) (n+1) (featureGrowth C g q n) _
      (featureGrowth_nonneg C g q hC n)
      (sourceMomentClass_succ_moment alpha K hK mu hmu n).1
      (sourceMomentClass_succ_moment alpha K hK mu hmu n).2 (hvalue n)
  let F := sourceWeightedFeatureMap c p phi
  let Q := sourceObjectiveAnchorFactor c p C3 phi G
  let R := sourceMomentRadius c C g p q K D alpha
  have hbounds := source_measure_region_objective_bounds c C g p q K D alpha C3 phi
    (sourceMomentClass alpha K) hc hC hp hq hK hD (fun n => (hphi n).continuous)
    (sourceMomentClass_isProbabilityMeasure alpha K)
    (fun nu hnu n => (sourceMomentClass_succ_moment alpha K hK nu hnu n).1)
    (fun nu hnu n => (sourceMomentClass_succ_moment alpha K hK nu hnu n).2)
    hvalue G U hU hSU hG hthirdG
  have hQR : Q * R^2 ≤ (L : Real) := by
    have hQ : 0 ≤ Q := le_trans (by norm_num) hbounds.1
    have hR : 1 ≤ R := one_le_sourceMomentRadius c C g p q K D alpha hC hK.le (by linarith)
    have hpow : R^2 ≤ R^3 := pow_le_pow_right₀ hR (by norm_num)
    rw [hL]
    change Q*R^2 ≤ 4*Q*R^3
    calc
      _ ≤ Q*R^3 := mul_le_mul_of_nonneg_left hpow hQ
      _ ≤ _ := by nlinarith [mul_nonneg hQ (pow_nonneg (by linarith : 0 ≤ R) 3)]
  have hobj := source_measure_region_objective_value_sub_le c C g p q K D alpha C3 phi
    (sourceMomentClass alpha K) hc hC hp hq hK hD (fun n => (hphi n).continuous)
    (sourceMomentClass_isProbabilityMeasure alpha K)
    (fun nu hnu n => (sourceMomentClass_succ_moment alpha K hK nu hnu n).1)
    (fun nu hnu n => (sourceMomentClass_succ_moment alpha K hK nu hnu n).2)
    hvalue G U hU hSU hG hthirdG (empiricalMomentMap F X) (∫ z, F z ∂mu)
    (empiricalMomentMap_mem_measureMomentRegion F _ D X hX)
    (population_integral_mem_measureMomentRegion F _ D mu hmu)
  have hscaled := scaled_empirical_population_moment_difference_le_residual mu id
    c C g p q K D alpha L phi hc hC hp hq hK hD aestronglyMeasurable_id
    (fun n => (hphi n).continuous)
    (fun n => (sourceMomentClass_succ_moment alpha K hK mu hmu n).1)
    (fun n => (sourceMomentClass_succ_moment alpha K hK mu hmu n).2) hvalue X hX 0
  have hdis := (feature_interpolated_momentResidual_le (fun i => X i) (fun i => Y i) phi
    (fun n => ∫ z, phi n z ∂mu) c C g p q K D alpha L 1 hN hc hC hp hq hK hD
    (by norm_num) hX hY hdiff hderiv hvalue hpop).2
  simp only [momentResidual,momentResidualTerm,one_smul,add_sub_cancel] at hdis
  dsimp only [momentResidual,momentResidualTerm,id_eq] at hscaled
  refine ⟨source_feature_integrable_of_source_class c C g p q alpha K phi hc hC hp hq hK hphi hgrowth mu hmu, ?_⟩
  have hfinal := (hobj.trans (mul_le_mul_of_nonneg_right hQR (norm_nonneg _))).trans
    (hscaled.trans hdis)
  simpa only [weightedSampleResidual, momentResidual, momentResidualTerm,
    finiteFeatureMean, normalizedDiscrepancy, Fintype.card_fin, F,
    WithLp.toLp_sub,WithLp.toLp_ofLp] using hfinal

/-- The standard objective lift uses the same radius/localization/Gamma event;
this purely scalar step adds no probability loss. -/
theorem source_objective_tracking_lift
    (r gap Lambda delta Ebound : Real)
    (hLambda : 0 ≤ Lambda) (hr : r ≤ Ebound)
    (hgap : gap ≤ Lambda*r+delta) :
    gap ≤ Lambda*Ebound+delta := by
  exact hgap.trans (add_le_add (mul_le_mul_of_nonneg_left hr hLambda) le_rfl)

end PaperFormalization.Manuscript
