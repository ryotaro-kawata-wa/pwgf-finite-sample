import PaperFormalization.Manuscript.VarianceCosineExampleThresholds

/-! # The displayed empirical functional is the same source objective
M13w verified implementation; source correspondence and axiom audit passed. Finite P2 integrability and actual empirical
normalization are checked before the objective identity is used. The extra
late-time quantity is the EMPIRICAL objective excess, not the population one.
-/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace PaperFormalization.Manuscript
set_option autoImplicit false

noncomputable def varianceCosinePairFunctionalError (P : VarianceCosineExampleParameters)
    {N : Nat} (mu : Measure VarianceCosinePoint) (X Y : SourceFiniteConfiguration N 1) : Real :=
  norm (X-Y)/Real.sqrt N+
    abs (varianceCosineFunctional P.a P.beta (finiteEmpiricalMeasure (fun i => X i))-
      varianceCosineFunctional P.a P.beta mu)
noncomputable def varianceCosineEmpiricalExcess (P : VarianceCosineExampleParameters)
    {N : Nat} (X : SourceFiniteConfiguration N 1) : Real :=
  varianceCosineFunctional P.a P.beta (finiteEmpiricalMeasure (fun i => X i))+P.beta

noncomputable def varianceCosineExampleError (P : VarianceCosineExampleParameters) {N : Nat}
    (mu0 : Measure VarianceCosinePoint) (T : Real) (w : VarianceCosineCouplingSpace N) (t : Real) :=
  varianceCosinePairFunctionalError P (varianceCosineExamplePopulation P mu0 T w t)
    (varianceCosineExamplePair P T w t).1 (varianceCosineExamplePair P T w t).2
noncomputable def varianceCosineExampleLateError (P : VarianceCosineExampleParameters) {N : Nat}
    (mu0 : Measure VarianceCosinePoint) (T : Real) (w : VarianceCosineCouplingSpace N) (t : Real) :=
  varianceCosineExampleError P mu0 T w t+
    varianceCosineEmpiricalExcess P (varianceCosineExamplePair P T w t).1
noncomputable def varianceCosineExamplePreError (P : VarianceCosineExampleParameters) {N : Nat}
    (mu0 : Measure VarianceCosinePoint) (T : Real) (w : VarianceCosineCouplingSpace N) :=
  varianceCosinePairFunctionalError P (varianceCosineExamplePrePopulation P mu0)
    (varianceCosineModelBranches P.a P.beta P.tau P.eta T w 0 P.tau).1
    (varianceCosineModelBranches P.a P.beta P.tau P.eta T w 0 P.tau).2

instance varianceCosineExamplePopulation_probability (P : VarianceCosineExampleParameters) {N : Nat}
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (T : Real) (w : VarianceCosineCouplingSpace N) (t : Real) :
    IsProbabilityMeasure (varianceCosineExamplePopulation P mu0 T w t) := by
  unfold varianceCosineExamplePopulation
  infer_instance

instance varianceCosineExamplePrePopulation_probability (P : VarianceCosineExampleParameters)
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0] :
    IsProbabilityMeasure (varianceCosineExamplePrePopulation P mu0) := by
  unfold varianceCosineExamplePrePopulation
  infer_instance

/-- Every actual finite cloud has a true second moment; no localization needed. -/
theorem varianceCosineEmpirical_memLp {N : Nat} (hN : 0<N) (X : SourceFiniteConfiguration N 1) :
    MemLp (id : VarianceCosinePoint -> VarianceCosinePoint) 2
      (finiteEmpiricalMeasure (fun i => X i)) := by
  letI : Nonempty (Fin N) := ⟨ ⟨ 0,hN ⟩ ⟩
  let D := ∑ i : Fin N, norm (X i)
  have hD (i : Fin N) : norm (X i)<=D :=
    Finset.single_le_sum (fun j _ => norm_nonneg (X j)) (Finset.mem_univ i)
  have hm : MeasurableSet {x : VarianceCosinePoint | norm x<=D} :=
    measurableSet_le measurable_norm measurable_const
  have hmass := finiteEmpiricalMeasure_apply_eq_one (fun i => X i) {x | norm x<=D} hD
  apply MemLp.of_bound aestronglyMeasurable_id D
  rw [ae_iff]
  change (finiteEmpiricalMeasure (fun i => X i)) {x | norm x<=D}ᶜ=0
  rw [measure_compl hm (measure_ne_top _ _),hmass,measure_univ]
  simp

theorem varianceCosineEmpirical_objective {N : Nat} (hN : 0<N)
    (a beta : Real) (X : SourceFiniteConfiguration N 1) :
    varianceCosineObjective a beta (empiricalMomentMap varianceCosineEncodedFeature X) =
      varianceCosineFunctional a beta (finiteEmpiricalMeasure (fun i => X i)) := by
  letI : Nonempty (Fin N) := ⟨ ⟨ 0,hN ⟩ ⟩
  have h := (varianceCosineObjective_population_identity a beta _ (varianceCosineEmpirical_memLp hN X)).2
  rw [show integral (finiteEmpiricalMeasure (fun i => X i)) varianceCosineEncodedFeature =
      empiricalMomentMap varianceCosineEncodedFeature X from
    integral_sourceWeightedFeatureMap_finiteEmpiricalMeasure 1 2 varianceCosineFeature X] at h
  exact h

/-- Conversion of the two source quantities to the three printed quantities. -/
theorem varianceCosine_functional_transfer (P : VarianceCosineExampleParameters) {N : Nat} (hN : 0<N)
    (mu : Measure VarianceCosinePoint) [IsProbabilityMeasure mu]
    (h2 : MemLp (id : VarianceCosinePoint -> VarianceCosinePoint) 2 mu)
    (X Y : SourceFiniteConfiguration N 1) :
    let joint := max (norm (X-Y)/Real.sqrt N)
      (sourceObjectiveError varianceCosineEncodedFeature (varianceCosineObjective P.a P.beta) mu X)
    0<=varianceCosineEmpiricalExcess P X ∧
      varianceCosinePairFunctionalError P mu X Y<=2*joint ∧
      varianceCosinePairFunctionalError P mu X Y+varianceCosineEmpiricalExcess P X <=
        3*joint+(varianceCosineObjective P.a P.beta (integral mu varianceCosineEncodedFeature)+P.beta) := by
  letI : Nonempty (Fin N) := ⟨ ⟨ 0,hN ⟩ ⟩
  have hx := varianceCosineEmpirical_objective hN P.a P.beta X
  have hy := (varianceCosineObjective_population_identity P.a P.beta mu h2).2
  have hlow := varianceCosineFunctional_lower P.a P.beta P.a_pos.le P.beta_pos.le _
    (varianceCosineEmpirical_memLp hN X)
  have hgap : sourceObjectiveError varianceCosineEncodedFeature (varianceCosineObjective P.a P.beta) mu X =
      abs (varianceCosineFunctional P.a P.beta (finiteEmpiricalMeasure (fun i => X i))-
        varianceCosineFunctional P.a P.beta mu) := by
    simp only [sourceObjectiveError,Real.norm_eq_abs,hx,hy]
  dsimp only
  rw [hgap]
  have h1 := le_max_left (norm (X-Y)/Real.sqrt N)
    (abs (varianceCosineFunctional P.a P.beta (finiteEmpiricalMeasure (fun i => X i))-
      varianceCosineFunctional P.a P.beta mu))
  have h2m := le_max_right (norm (X-Y)/Real.sqrt N)
    (abs (varianceCosineFunctional P.a P.beta (finiteEmpiricalMeasure (fun i => X i))-
      varianceCosineFunctional P.a P.beta mu))
  have hdiff := le_abs_self (varianceCosineFunctional P.a P.beta (finiteEmpiricalMeasure (fun i => X i))-
    varianceCosineFunctional P.a P.beta mu)
  unfold varianceCosineEmpiricalExcess varianceCosinePairFunctionalError
  rw [hy]
  exact ⟨ by linarith,by linarith,by linarith ⟩

theorem varianceCosineExamplePopulation_memLp (P : VarianceCosineExampleParameters) {N : Nat}
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (hU : ∀ᵐ u ∂ mu0, norm u<=P.radius) (T : Real) (w : VarianceCosineCouplingSpace N) (t : Real) :
    MemLp (id : VarianceCosinePoint -> VarianceCosinePoint) 2 (varianceCosineExamplePopulation P mu0 T w t) :=
  varianceCosinePopulation_memLp mu0 P.radius P.radius_nonneg hU _ _

theorem varianceCosineExampleError_nonneg (P : VarianceCosineExampleParameters) {N : Nat}
    (mu0 : Measure VarianceCosinePoint) (T : Real) (w : VarianceCosineCouplingSpace N) (t : Real) :
    0<=varianceCosineExampleError P mu0 T w t := by
  unfold varianceCosineExampleError varianceCosinePairFunctionalError
  positivity

end PaperFormalization.Manuscript
