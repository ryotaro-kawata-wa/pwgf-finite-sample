import PaperFormalization.Manuscript.ConditionalPathMarginal
import Mathlib.Probability.Kernel.CondDistrib

/-! # The original common conditional path law is constructed, not assumed

M13o declarations checked with the pinned toolchain; see verification/latest.json.
Given one measurable standard-Borel-valued path observation, construct its regular
conditional law given the population environment. The exact joint law, common
pushforward marginals and AE uniqueness are derived. This does not identify a
Gaussian/covariance prehistory with the population environment.
-/
open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory
namespace PaperFormalization.Manuscript
variable {O S P E : Type*} [MeasurableSpace O] [MeasurableSpace S]
  [MeasurableSpace P] [StandardBorelSpace P] [Nonempty P] [MeasurableSpace E]

noncomputable def originalConditionalPathLaw (nu : Measure O) [IsFiniteMeasure nu]
    (environment : O → S) (paths : O → P) : Kernel S P :=
  condDistrib paths environment nu

instance originalConditionalPathLaw_markov (nu : Measure O) [IsFiniteMeasure nu]
    (environment : O → S) (paths : O → P) :
    IsMarkovKernel (originalConditionalPathLaw nu environment paths) := by
  unfold originalConditionalPathLaw
  infer_instance

/-- Exact disintegration of the ORIGINAL joint environment/path law. -/
theorem originalConditionalPathLaw_joint (nu : Measure O) [IsFiniteMeasure nu]
    (environment : O → S) (paths : O → P) (hpaths : Measurable paths) :
    nu.map (fun x => (environment x, paths x)) =
      (nu.map environment) ⊗ₘ originalConditionalPathLaw nu environment paths :=
  (compProd_map_condDistrib hpaths.aemeasurable).symm

/-- Every chosen evaluation uses this same path kernel, with a pointwise exact
pushforward identity; no new conditional version is independently chosen. -/
theorem originalConditionalPathLaw_marginal (nu : Measure O) [IsFiniteMeasure nu]
    (environment : O → S) (paths : O → P) (eval : S → P → E)
    (heval : Measurable (fun z : S × P => eval z.1 z.2)) :
    IsMarkovKernel (conditionalPathMarginal (originalConditionalPathLaw nu environment paths) eval) ∧
      ∀ h, conditionalPathMarginal (originalConditionalPathLaw nu environment paths) eval h =
        (originalConditionalPathLaw nu environment paths h).map (eval h) :=
  conditionalPathMarginal_properties _ eval heval

/-- A competing original-law disintegration agrees as a PATH measure on one AE
environment set. This is stronger than separately choosing versions at each time. -/
theorem originalConditionalPathLaw_unique (nu : Measure O) [IsFiniteMeasure nu]
    (environment : O → S) (paths : O → P)
    (henvironment : Measurable environment) (hpaths : Measurable paths)
    (candidate : Kernel S P) [IsFiniteKernel candidate]
    (hjoint : nu.map (fun x => (environment x, paths x)) = nu.map environment ⊗ₘ candidate) :
    originalConditionalPathLaw nu environment paths =ᵐ[nu.map environment] candidate :=
  condDistrib_ae_eq_of_measure_eq_compProd_of_measurable henvironment hpaths hjoint

/-- Measure-level uniqueness transfers simultaneously to an arbitrary family of
pushforwards; it does not use a union of uncountably many null sets. -/
theorem originalConditionalPathLaw_all_marginals_unique
    {I : Type*} (nu : Measure O) [IsFiniteMeasure nu]
    (environment : O → S) (paths : O → P)
    (henvironment : Measurable environment) (hpaths : Measurable paths)
    (candidate : Kernel S P) [IsFiniteKernel candidate]
    (hjoint : nu.map (fun x => (environment x, paths x)) = nu.map environment ⊗ₘ candidate)
    (eval : I → S → P → E) :
    ∀ᵐ h ∂nu.map environment, ∀ i,
      (originalConditionalPathLaw nu environment paths h).map (eval i h) =
        (candidate h).map (eval i h) := by
  filter_upwards [originalConditionalPathLaw_unique nu environment paths
    henvironment hpaths candidate hjoint] with h hh
  intro i
  rw [hh]

/-- For a fixed measurable evaluation the conventional conditional distribution
agrees AE with the common-kernel pushforward. The qualifier is per evaluation. -/
theorem originalConditionalPathLaw_eval_condDistrib
    [StandardBorelSpace E] [Nonempty E]
    (nu : Measure O) [IsFiniteMeasure nu] (environment : O → S) (paths : O → P)
    (hpaths : Measurable paths) (eval : P → E) (heval : Measurable eval) :
    condDistrib (eval ∘ paths) environment nu =ᵐ[nu.map environment]
      (originalConditionalPathLaw nu environment paths).map eval :=
  condDistrib_comp environment hpaths.aemeasurable heval
end PaperFormalization.Manuscript
