import PaperFormalization.Manuscript.SourceObjectiveResidual
import PaperFormalization.Manuscript.SourceFinalTrackingStatement
import PaperFormalization.Manuscript.SourceGammaTraceTransfer

/-! # Scalar objective tracking on the same event as particle tracking

M13t verified implementation. These are definitions of OUTPUT certificates,
not additional hypotheses of the source-facing theorem. The population objective
uses its genuine Bochner moment. Right and strict-prefix pretrace conclusions
are separate. Equality of the two particle configurations need not imply equality
with the population objective: even at zero discrepancy the residual delta remains.
-/
open MeasureTheory Set
open scoped NNReal BigOperators
namespace PaperFormalization.Manuscript
open Continuous Piecewise
variable {N d : Nat}
variable {H : Nat -> Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace Real (H n)] [∀ n, CompleteSpace (H n)]

noncomputable def sourceObjectiveError
    (F : EuclideanSpace Real (Fin d) -> lp H 2) (G : lp H 2 -> Real)
    (mu : Measure (EuclideanSpace Real (Fin d)))
    (X : SourceFiniteConfiguration N d) : Real :=
  norm (G (empiricalMomentMap F X) - G (∫ x, F x ∂mu))

/-- Simultaneous value control and genuine moment integrability. -/
def SourceObjectiveControl
    (F : EuclideanSpace Real (Fin d) -> lp H 2) (G : lp H 2 -> Real)
    (law : Real -> Measure (EuclideanSpace Real (Fin d)))
    (preLaw : Nat -> Measure (EuclideanSpace Real (Fin d)))
    (X Y : Real -> SourceFiniteConfiguration N d)
    (preX preY : Nat -> SourceFiniteConfiguration N d)
    (J : Nat) (T Lambda delta : Real) : Prop :=
  (∀ t ∈ Icc 0 T, Integrable F (law t) ∧
    sourceObjectiveError F G (law t) (X t) ≤ Lambda * (norm (X t-Y t)/Real.sqrt N) + delta) ∧
  (∀ k < J, Integrable F (preLaw k) ∧
    sourceObjectiveError F G (preLaw k) (preX k) ≤ Lambda * (norm (preX k-preY k)/Real.sqrt N) + delta)

/-- The objective analogue of the fixed-schedule estimate; the delta term
is present also when the particle discrepancy happens to vanish. -/
def SourceObjectiveTrackingConclusion
    (F : EuclideanSpace Real (Fin d) -> lp H 2) (G : lp H 2 -> Real)
    (law : Real -> Measure (EuclideanSpace Real (Fin d)))
    (preLaw : Nat -> Measure (EuclideanSpace Real (Fin d)))
    (X : Real -> SourceFiniteConfiguration N d) (preX : Nat -> SourceFiniteConfiguration N d)
    (kappa : Real -> Real) (tau eta : Nat -> Real)
    (J : Nat) (T Lambda delta deltaTilde A : Real) : Prop :=
  (∀ t ∈ Icc 0 T, Integrable F (law t) ∧
    sourceObjectiveError F G (law t) (X t) ≤
      Lambda * (Real.exp (1/4) * jumpAmplification (sourceJumpError A eta) J *
        sourceCurvatureEnvelope kappa tau eta delta deltaTilde A J t) + delta) ∧
  (∀ k < J, Integrable F (preLaw k) ∧
    sourceObjectiveError F G (preLaw k) (preX k) ≤
      Lambda * (Real.exp (1/4) * jumpAmplification (sourceJumpError A eta) J *
        sourceCurvatureEnvelope kappa tau eta delta deltaTilde A k (tau (k+1))) + delta)

/-- No additional event or probability expenditure is used in this lift. -/
theorem source_objective_conclusion_of_tracking
    (F : EuclideanSpace Real (Fin d) -> lp H 2) (G : lp H 2 -> Real)
    (law preLaw) (X Y : Real -> SourceFiniteConfiguration N d)
    (preX preY : Nat -> SourceFiniteConfiguration N d)
    (kappa : Real -> Real) (tau eta : Nat -> Real)
    (J : Nat) (T Lambda delta deltaTilde A : Real) (hLambda : 0 ≤ Lambda)
    (hControl : SourceObjectiveControl F G law preLaw X Y preX preY J T Lambda delta)
    (hTracking : SourceTrackingConclusion X Y preX preY kappa tau eta J T delta deltaTilde A) :
    SourceObjectiveTrackingConclusion F G law preLaw X preX kappa tau eta J T Lambda delta deltaTilde A := by
  constructor
  · intro t ht
    exact ⟨(hControl.1 t ht).1,
      source_objective_tracking_lift _ _ _ _ _ hLambda (hTracking.1 t ht) (hControl.1 t ht).2⟩
  · intro k hk
    exact ⟨(hControl.2 k hk).1,
      source_objective_tracking_lift _ _ _ _ _ hLambda (hTracking.2.2.1 k hk) (hControl.2 k hk).2⟩

set_option maxHeartbeats 3000000 in
/-- Derive all-time objective control from the original closed-label data.
The label selector includes a terminal singleton and never identifies pre/post laws. -/
theorem source_objective_control_of_closed_labels
    {Seed : Type*} [MeasurableSpace Seed]
    (c C g p q K D alpha C3 : Real) (phi : ∀ n, EuclideanSpace Real (Fin d) -> H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hK : 0 < K) (hD : 1 ≤ D)
    (hphi : ∀ n, ContDiff Real 2 (phi n))
    (hgrowth : ∀ n z k, k ≤ 2 -> norm (iteratedFDeriv Real k (phi n) z) ≤
      featureGrowth C g q n * (1+norm z^(n+1-k)))
    (G : lp H 2 -> Real) (U : Set (lp H 2)) (hU : IsOpen U)
    (hSU : measureMomentRegion (sourceWeightedFeatureMap c p phi) (sourceMomentClass alpha K) D ⊆ U)
    (hG : ContDiffOn Real 3 G U)
    (hthirdG : ∀ theta, theta ∈ measureMomentRegion (sourceWeightedFeatureMap c p phi)
      (sourceMomentClass alpha K) D -> norm (iteratedFDeriv Real 3 G theta) ≤ C3)
    (L : NNReal) (hL : (L : Real) = sourceComparisonEnvelope c C g p q K D alpha C3 phi G)
    (mu0 : Measure Seed) (hN : 0 < N)
    (tau : Nat -> Real) (J : Nat) (T delta : Real)
    (htau0 : tau 0 = 0) (htime : ∀ k < J, tau k < tau (k+1))
    (Z : Nat -> Seed -> Real -> EuclideanSpace Real (Fin d))
    (XB YB : Nat -> Real -> SourceFiniteConfiguration N d)
    (hClass : ∀ k ≤ J, ∀ t ∈ Icc (tau k) (if k < J then tau (k+1) else T),
      mu0.map (fun u => Z k u t) ∈ sourceMomentClass alpha K)
    (hLocal : ∀ k ≤ J, ∀ t ∈ Icc (tau k) (if k < J then tau (k+1) else T),
      ∀ i, norm (XB k t i) ≤ D ∧ norm (YB k t i) ≤ D)
    (hGamma : ∀ k ≤ J, ∀ t ∈ Icc (tau k) (if k < J then tau (k+1) else T),
      weightedSampleResidual (featureResidualWeight c p L) phi
        (fun n => ∫ u, phi n (Z k u t) ∂mu0) (fun i => YB k t i) ≤ delta) :
    SourceObjectiveControl (sourceWeightedFeatureMap c p phi) G
      (fun t => mu0.map (fun u => sourceGlue tau J (fun k => Z k u) t))
      (fun k => mu0.map (fun u => Z k u (tau (k+1))))
      (sourceGlue tau J XB) (sourceGlue tau J YB)
      (fun k => XB k (tau (k+1))) (fun k => YB k (tau (k+1)))
      J T (featureDisplacementLambda c C g p q D L) delta := by
  have hclosed k (hk : k ≤ J) t (ht : t ∈ Icc (tau k) (if k < J then tau (k+1) else T)) :
      Integrable (sourceWeightedFeatureMap c p phi) (mu0.map (fun u => Z k u t)) ∧
      sourceObjectiveError (sourceWeightedFeatureMap c p phi) G (mu0.map (fun u => Z k u t)) (XB k t) ≤
        featureDisplacementLambda c C g p q D L * (norm (XB k t-YB k t)/Real.sqrt N) + delta := by
    have heq := weightedSampleResidual_marginal_eq_representative mu0
      (fun u => Z k u t) (fun u => Z k u t)
      (sourceMomentClass_isProbabilityMeasure alpha K _ (hClass k hk t ht))
      Filter.EventuallyEq.rfl (fun i => YB k t i) (fun i => YB k t i) rfl
      (featureResidualWeight c p L) phi (fun n => (hphi n).continuous)
    have hg := hGamma k hk t ht
    rw [← heq] at hg
    have ho := source_objective_gap_le_discrepancy_and_residual
      c C g p q K D alpha C3 phi hc hC hp hq hK hD hphi hgrowth
      G U hU hSU hG hthirdG L hL _ (hClass k hk t ht) (XB k t) (YB k t) hN
      (fun i => (hLocal k hk t ht i).1) (fun i => (hLocal k hk t ht i).2)
    exact ⟨ho.1, ho.2.trans (add_le_add le_rfl hg)⟩
  constructor
  · intro t ht
    obtain ⟨k,hk,hkt,hstrict⟩ := exists_schedule_right_label tau J T t htau0 ht
    have hx := sourceGlue_on_branch tau J XB htime k hk t hkt.1 hstrict
    have hy := sourceGlue_on_branch tau J YB htime k hk t hkt.1 hstrict
    have hz : (fun u => sourceGlue tau J (fun k => Z k u) t) = (fun u => Z k u t) := by
      funext u
      exact sourceGlue_on_branch tau J (fun k => Z k u) htime k hk t hkt.1 hstrict
    simpa only [hz,hx,hy,sourceObjectiveError] using hclosed k hk t hkt
  · intro k hk
    have ht : tau (k+1) ∈ Icc (tau k) (if k < J then tau (k+1) else T) := by
      rw [if_pos hk]; exact ⟨(htime k hk).le,le_rfl⟩
    exact hclosed k hk.le (tau (k+1)) ht

end PaperFormalization.Manuscript
