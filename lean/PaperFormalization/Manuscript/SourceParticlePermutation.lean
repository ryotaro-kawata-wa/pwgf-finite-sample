import PaperFormalization.Manuscript.SourceWhiteningPermutation
import PaperFormalization.Manuscript.SourceActualGramRegularity
import PaperFormalization.Manuscript.SourceParticleUnflatten

/-! # Actual empirical and population coefficients under particle permutations
M13r verified unit (see CODEX_HANDOFF_M13R.md). These are coefficient identities, not a claim of independence
of empirical particles or a completed exchangeability theorem for the global
ODE solution map. All original normalization factors are left unchanged.
-/
open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Matrix.Norms.Frobenius
namespace PaperFormalization.Manuscript
variable {N d : Nat}

def sourceParticlePermute (s : Equiv.Perm (Fin N))
    (X : PiLp 2 (fun _ : Fin N => EuclideanSpace Real (Fin d))) :=
  WithLp.toLp 2 (fun i => X (s i))

def sourceParticleIndexPermute (s : Equiv.Perm (Fin N)) : Equiv.Perm (Fin N × Fin d) :=
  Equiv.prodCongr s (Equiv.refl (Fin d))

@[simp] theorem sourceParticlePermute_flatten (s : Equiv.Perm (Fin N))
    (X : PiLp 2 (fun _ : Fin N => EuclideanSpace Real (Fin d))) :
    particleFlatten (sourceParticlePermute s X) =
      sourceEuclideanPermute (sourceParticleIndexPermute s) (particleFlatten X) := rfl

theorem sourceParticlePermute_measurable (s : Equiv.Perm (Fin N)) :
    Measurable (sourceParticlePermute (d := d) s) := by
  apply (WithLp.measurable_toLp 2 _).comp
  exact measurable_pi_lambda _ (fun i => (measurable_pi_apply (s i)).comp (WithLp.measurable_ofLp 2 _))

/-- Particle permutations leave the exact empirical mean unchanged. -/
theorem source_empiricalMomentMap_permute
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (J : EuclideanSpace Real (Fin d) -> E) (s : Equiv.Perm (Fin N))
    (X : PiLp 2 (fun _ : Fin N => EuclideanSpace Real (Fin d))) :
    empiricalMomentMap J (sourceParticlePermute s X) = empiricalMomentMap J X := by
  unfold empiricalMomentMap
  congr 1
  exact Fintype.sum_equiv s _ _ (fun _ => rfl)

/-- The ACTUAL configuration drift commutes with particle permutations. -/
theorem source_empiricalConfigurationField_permute
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (J : EuclideanSpace Real (Fin d) -> E)
    (V : E × EuclideanSpace Real (Fin d) -> EuclideanSpace Real (Fin d))
    (s : Equiv.Perm (Fin N)) (X : PiLp 2 (fun _ : Fin N => EuclideanSpace Real (Fin d))) :
    empiricalConfigurationField J V (sourceParticlePermute s X) =
      sourceParticlePermute s (empiricalConfigurationField J V X) := by
  unfold empiricalConfigurationField
  rw [source_empiricalMomentMap_permute]
  rfl

/-- The frozen-population vector field has the same coordinate symmetry. -/
theorem source_frozenConfigurationField_permute
    {E : Type*} (theta : E)
    (V : E × EuclideanSpace Real (Fin d) -> EuclideanSpace Real (Fin d))
    (s : Equiv.Perm (Fin N)) (X : PiLp 2 (fun _ : Fin N => EuclideanSpace Real (Fin d))) :
    frozenMomentConfigurationField V theta (sourceParticlePermute s X) =
      sourceParticlePermute s (frozenMomentConfigurationField V theta X) := rfl

variable {H : Nat -> Type*} [forall m, NormedAddCommGroup (H m)]
  [forall m, InnerProductSpace Real (H m)] [forall m, CompleteSpace (H m)]

/-- The empirical 1/sqrt(N) Hessian factor is reindexed, never rescaled. -/
theorem source_empiricalKernelFactor_permute
    (c p : Real) (phi : forall m, EuclideanSpace Real (Fin d) -> H m)
    (G : lp H 2 -> Real) (s : Equiv.Perm (Fin N))
    (X : PiLp 2 (fun _ : Fin N => EuclideanSpace Real (Fin d))) :
    sourceEmpiricalKernelFactor c p phi G (sourceParticlePermute s X) =
      sourceMatrixPermute (sourceParticleIndexPermute s) (sourceEmpiricalKernelFactor c p phi G X) := by
  unfold sourceEmpiricalKernelFactor
  rw [source_empiricalMomentMap_permute]
  rfl

/-- Fixed Gram versions reindex exactly, including the values outside the
moment domain. This algebraic equality is not an integrability assertion. -/
theorem sourcePopulationGramVersion_permute
    {S E : Type*} [MeasurableSpace S]
    [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
    (kappa : Kernel S (EuclideanSpace Real (Fin d)))
    (J : EuclideanSpace Real (Fin d) -> E) (G : E -> Real) (U : Set E) (anchor : E)
    (Y : S -> Fin N -> EuclideanSpace Real (Fin d)) (s : Equiv.Perm (Fin N)) (h : S) :
    sourcePopulationGramVersion kappa J G U anchor (fun h i => Y h (s i)) h =
      sourceMatrixPermute (sourceParticleIndexPermute s) (sourcePopulationGramVersion kappa J G U anchor Y h) := by
  ext i j
  rfl
end PaperFormalization.Manuscript
