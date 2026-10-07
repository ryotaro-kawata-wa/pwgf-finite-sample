import PaperFormalization.Manuscript.VarianceCosineExampleParameters
import Mathlib.Probability.Independence.Basic

/-! # The exact original product law and one-step auxiliary space
M13w verified implementation; source correspondence and axiom audit passed. This identifies the spaces already used by M13U
and M13T; it does not resample the canonical coordinate or condition a law.
-/
open MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology
namespace PaperFormalization.Manuscript
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev VarianceCosineOriginalSpace (N : Nat) := SourceFiniteConfiguration N 1 × Real
abbrev VarianceCosineExampleTower (N : Nat) :=
  SourceAuxiliarySpace (VarianceCosineOriginalSpace N) (SourceStepNormal N 1) 1

noncomputable def varianceCosineOriginalLaw (N : Nat) (mu0 : Measure VarianceCosinePoint) :=
  (sourceInitialConfigurationLaw (N := N) mu0).prod (gaussianReal 0 1)
noncomputable def varianceCosineExampleTowerLaw (N : Nat) (mu0 : Measure VarianceCosinePoint) :=
  sourceAuxiliaryMeasure (varianceCosineOriginalLaw N mu0) (stdGaussian (SourceStepNormal N 1)) 1

def varianceCosineOriginalInitial {N : Nat} (o : VarianceCosineOriginalSpace N) := o.1
def varianceCosineOriginalInnovation {N : Nat} (n : Nat) (o : VarianceCosineOriginalSpace N) :=
  varianceCosineInnovation n o.2

def varianceCosineTowerInverse {N : Nat} (w : VarianceCosineCouplingSpace N) :
    VarianceCosineExampleTower N := (ULift.up (w.1,w.2.1),w.2.2)

theorem varianceCosineTower_left_inverse {N : Nat} (z : VarianceCosineExampleTower N) :
    varianceCosineTowerInverse (varianceCosineTowerCoordinates z) = z := by
  rcases z with ⟨ ⟨ u ⟩,h ⟩
  rfl

theorem varianceCosineTower_right_inverse {N : Nat} (w : VarianceCosineCouplingSpace N) :
    varianceCosineTowerCoordinates (varianceCosineTowerInverse w) = w := rfl

theorem varianceCosineTowerInverse_measurable {N : Nat} :
    Measurable (varianceCosineTowerInverse (N := N)) := by
  unfold varianceCosineTowerInverse
  fun_prop

instance varianceCosineOriginalLaw_probability (N : Nat) (mu0 : Measure VarianceCosinePoint)
    [IsProbabilityMeasure mu0] : IsProbabilityMeasure (varianceCosineOriginalLaw N mu0) := by
  unfold varianceCosineOriginalLaw
  infer_instance

instance varianceCosineExampleTowerLaw_probability (N : Nat) (mu0 : Measure VarianceCosinePoint)
    [IsProbabilityMeasure mu0] : IsProbabilityMeasure (varianceCosineExampleTowerLaw N mu0) := by
  unfold varianceCosineExampleTowerLaw
  infer_instance

instance varianceCosineModelLaw_probability (N : Nat) (mu0 : Measure VarianceCosinePoint)
    [IsProbabilityMeasure mu0] : IsProbabilityMeasure (varianceCosineModelLaw N mu0) := by
  unfold varianceCosineModelLaw
  infer_instance

theorem varianceCosineTowerInverse_preserving {N : Nat}
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0] :
    MeasurePreserving varianceCosineTowerInverse (varianceCosineModelLaw N mu0)
      (varianceCosineExampleTowerLaw N mu0) := by
  have hp := varianceCosineTower_preserving (sourceInitialConfigurationLaw (N := N) mu0)
  have hmap : (varianceCosineExampleTowerLaw N mu0).map varianceCosineTowerCoordinates =
      varianceCosineModelLaw N mu0 := hp.map_eq
  refine ⟨ varianceCosineTowerInverse_measurable,?_ ⟩
  calc
    _ = ((varianceCosineExampleTowerLaw N mu0).map varianceCosineTowerCoordinates).map
        varianceCosineTowerInverse := by rw [hmap]
    _ = (varianceCosineExampleTowerLaw N mu0).map id := by
      rw [Measure.map_map varianceCosineTowerInverse_measurable hp.measurable]
      congr 1
    _ = _ := by simp

theorem varianceCosineOriginalInitial_measurable {N : Nat} :
    Measurable (varianceCosineOriginalInitial (N := N)) := measurable_fst

theorem varianceCosineOriginalInnovation_measurable {N : Nat} (n : Nat) :
    Measurable (varianceCosineOriginalInnovation (N := N) n) := by
  unfold varianceCosineOriginalInnovation varianceCosineInnovation
  split_ifs <;> fun_prop

theorem varianceCosineOriginal_initial_law {N : Nat}
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0] (i : Fin N) :
    (varianceCosineOriginalLaw N mu0).map (fun o => varianceCosineOriginalInitial o i) = mu0 := by
  have hp : MeasurePreserving (Prod.fst : VarianceCosineOriginalSpace N -> _)
      (varianceCosineOriginalLaw N mu0) (sourceInitialConfigurationLaw mu0) := measurePreserving_fst
  calc
    _ = ((varianceCosineOriginalLaw N mu0).map Prod.fst).map (fun U => U i) :=
      (Measure.map_map (by fun_prop) measurable_fst).symm
    _ = mu0 := by rw [hp.map_eq,varianceCosineInitial_marginal]

theorem varianceCosineOriginal_iid {N : Nat}
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0] :
    iIndepFun (fun (i : Fin N) o => varianceCosineOriginalInitial o i) (varianceCosineOriginalLaw N mu0) :=
  source_iIndepFun_pullback (sourceInitialConfigurationLaw mu0) (varianceCosineOriginalLaw N mu0)
    Prod.fst measurePreserving_fst (fun i U => U i) (by intro i; fun_prop)
    (varianceCosineInitial_iid mu0)

theorem varianceCosineOriginal_population_independent {N : Nat}
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0] :
    IndepFun (fun o n => varianceCosineOriginalInnovation (N := N) n o)
      (fun o i => varianceCosineOriginalInitial o i) (varianceCosineOriginalLaw N mu0) := by
  have hh : Measurable (fun Z n => varianceCosineInnovation n Z) := by
    apply measurable_pi_lambda
    intro n
    unfold varianceCosineInnovation
    split_ifs <;> fun_prop
  exact (indepFun_prod (by fun_prop : Measurable (fun U : SourceFiniteConfiguration N 1 => fun i => U i)) hh).symm

theorem varianceCosineOriginal_environment_law {N : Nat}
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0] :
    (varianceCosineOriginalLaw N mu0).map (fun o n => varianceCosineOriginalInnovation n o) =
      (gaussianReal 0 1).map (fun Z n => varianceCosineInnovation n Z) := by
  have hm : Measurable (fun Z n => varianceCosineInnovation n Z) := by
    apply measurable_pi_lambda
    intro n
    unfold varianceCosineInnovation
    split_ifs <;> fun_prop
  have hp : MeasurePreserving (Prod.snd : VarianceCosineOriginalSpace N -> Real)
      (varianceCosineOriginalLaw N mu0) (gaussianReal 0 1) := measurePreserving_snd
  rw [show (fun o n => varianceCosineOriginalInnovation (N := N) n o) =
    (fun Z n => varianceCosineInnovation n Z) ∘ Prod.snd by rfl,
    <- Measure.map_map hm measurable_snd,hp.map_eq]

theorem varianceCosineOriginal_fresh {N : Nat}
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0] (n : Fin 1) :
    IndepFun (sourceOriginalPrehistory (varianceCosineOriginalInitial (N := N))
      varianceCosineOriginalInnovation n) (varianceCosineOriginalInnovation n)
      (varianceCosineOriginalLaw N mu0) := by
  fin_cases n
  have he : sourceOriginalPrehistory (varianceCosineOriginalInitial (N := N))
      varianceCosineOriginalInnovation 0 =
      fun o => ((fun i : Fin 0 => Fin.elim0 i : Fin 0 -> Real),o.1) := by
    funext o
    apply Prod.ext
    . funext i; exact Fin.elim0 i
    . rfl
  rw [he]
  change IndepFun (fun o : VarianceCosineOriginalSpace N =>
      ((fun i : Fin 0 => Fin.elim0 i : Fin 0 -> Real),o.1)) (fun o => o.2) _
  exact indepFun_prod (measurable_const.prodMk measurable_id) measurable_id

theorem varianceCosineOriginal_innovation_law {N : Nat}
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0] (n : Fin 1) :
    (varianceCosineOriginalLaw N mu0).map (varianceCosineOriginalInnovation n) = gaussianReal 0 1 := by
  fin_cases n
  exact (measurePreserving_snd : MeasurePreserving (Prod.snd : VarianceCosineOriginalSpace N -> Real)
    (varianceCosineOriginalLaw N mu0) (gaussianReal 0 1)).map_eq

/-- The packed innovation is pointwise the SAME pair (Z, auxiliary) as M13U. -/
theorem varianceCosineExample_packed {N : Nat} (z : VarianceCosineExampleTower N) :
    sourceTowerPacked varianceCosineOriginalInnovation 1 z =
      fun _ : Fin 1 => (varianceCosineTowerCoordinates z).2 := by
  funext i
  fin_cases i
  rfl

/-- The one-jump right-label selector includes the post value at tau. -/
theorem varianceCosineGlue_one {E : Type*} (tau : Real) (F : Nat -> Real -> E) (t : Real) :
    sourceGlue (varianceCosineTimes tau) 1 F t = F (if t<tau then 0 else 1) t := by
  classical
  by_cases ht : t<tau
  . simp [sourceGlue,Piecewise.jumpCount,varianceCosineTimes,ht,not_le.mpr ht]
  . simp [sourceGlue,Piecewise.jumpCount,varianceCosineTimes,ht,le_of_not_gt ht]

/-- The original characteristic depends only on the first population scalar. -/
theorem varianceCosineOriginalCharacteristic_formula
    (P : VarianceCosineExampleParameters) (T : Real) (e : Nat -> Real)
    (k : Nat) (hk : k<=1) (u : VarianceCosinePoint) (t : Real) :
    sourceOriginalCharacteristic (varianceCosineTimes P.tau) (varianceCosineAmplitudes P.eta)
      (varianceCosineFlowY P.a P.beta P.tau P.eta T) (varianceCosineField P.a P.beta) k e u t =
      varianceCosineAffine (varianceCosineBranchMeanY P.a P.beta P.tau P.eta T (e 0) k t)
        (Real.exp (-P.a*t)) u := by
  have hp : (fun i : Fin k => e i.val) = (fun _ => e 0) := by
    funext i
    have hi : i.val=0 := by omega
    rw [hi]
  unfold sourceOriginalCharacteristic
  rw [hp]
  exact varianceCosineReferenceBranch_formula P.a P.beta P.tau P.eta T (e 0) u k hk t

end PaperFormalization.Manuscript
