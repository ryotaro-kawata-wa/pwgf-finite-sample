import PaperFormalization.Manuscript.SourceOriginalCovarianceView
import PaperFormalization.Manuscript.SourceCausalReference

/-! # The actual causal reference sample, covariance view and full-history law

M13p verified unit (see CODEX_HANDOFF_M13P.md). A closed branch is constructed by the finite
flow/jump recursion. Its pre-law is proved equal to both view coefficients.
No equality between different conditional distributions is used or asserted.
-/
open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory
namespace PaperFormalization.Manuscript
variable {O Env W Aux : Type*} [MeasurableSpace O] [MeasurableSpace Env]
  [MeasurableSpace W] [MeasurableSpace Aux] {N d : ℕ}

/-- Discharge covariance observation/sample/pre-law compatibility in one unit.
The population environment may include future innovations, but `past` extracts
only the prefix used by the nth characteristic. Full Gaussian history retains
arbitrary additional initial/sample/auxiliary information in `Aux`.
Eligibility is compared as a property of one identical population measure. -/
theorem source_scheduled_covariance_identifications
    (nu : Measure O) [IsProbabilityMeasure nu]
    (mu0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure mu0]
    (environment : O -> Env) (initial : Fin N -> O -> EuclideanSpace ℝ (Fin d))
    (henv : Measurable environment) (hinit : ∀ i, Measurable (initial i))
    (hiid : iIndepFun initial nu) (hind : IndepFun environment (fun w i => initial i w) nu)
    (hlaw : ∀ i, nu.map (initial i) = mu0)
    (tau : ℕ -> ℝ)
    (flow : (n : ℕ) -> (Fin n -> W) -> ℝ -> EuclideanSpace ℝ (Fin d) -> EuclideanSpace ℝ (Fin d))
    (jump : (n : ℕ) -> (Fin n -> W) -> W -> EuclideanSpace ℝ (Fin d) -> EuclideanSpace ℝ (Fin d))
    (hflow : ∀ n t, Measurable (fun z : (Fin n -> W) × EuclideanSpace ℝ (Fin d) => flow n z.1 t z.2))
    (hjump : ∀ n, Measurable (fun z : ((Fin n -> W) × W) × EuclideanSpace ℝ (Fin d) =>
      jump n z.1.1 z.1.2 z.2))
    (n : ℕ) (past : Env -> Fin n -> W) (hpast : Measurable past)
    (alpha scale : ℝ) (halpha : 0 < alpha) (hscale : 0 < scale) :
    ∃ view : SourceObservedCovarianceView N d alpha
      (sourceExponentialMomentCoefficient alpha * scale) nu Env (Fin N -> EuclideanSpace ℝ (Fin d)),
      ∀ w (aux : Aux),
        view.X (view.observation w) =
          (fun i => sourceReferenceBranch tau flow jump n (past (environment w)) (initial i w) (tau (n+1))) ∧
        view.κ (view.observation w).1 =
          sourceFullHistoryPreLaw (Aux := Aux) mu0 tau flow jump n (past (environment w), aux) ∧
        view.κ (view.observation w).1 =
          mu0.map (fun u => sourceReferenceBranch tau flow jump n (past (environment w)) u (tau (n+1))) ∧
        ((view.observation w).1 ∈ view.PopGood ↔
          (past (environment w), aux) ∈ populationExponentialEligibility
            (sourceFullHistoryPreLaw (Aux := Aux) mu0 tau flow jump n) alpha scale) := by
  let Phi := fun e u => sourceReferencePre tau flow jump n (past e) u
  have hPhi : Measurable (fun z : Env × EuclideanSpace ℝ (Fin d) => Phi z.1 z.2) :=
    (sourceReferenceBranch_measurable tau flow jump hflow hjump n (tau (n+1))).comp
      ((hpast.comp measurable_fst).prodMk measurable_snd)
  let view := sourceOriginalCovarianceView nu mu0 environment initial henv hinit hiid hind hlaw
    Phi hPhi alpha scale halpha hscale
  refine ⟨view, ?_⟩
  intro w aux
  have hid := sourceCausalPreLaw_identity (Aux := Aux) mu0 tau flow jump hflow hjump n
    past hpast (environment w) aux
  refine ⟨rfl, hid.1, hid.1.trans hid.2, ?_⟩
  change (populationExponentialEligibility (characteristicKernel mu0 Phi) alpha scale
    (environment w)) ↔ _
  change (∫⁻ x, ENNReal.ofReal (Real.exp ((‖x‖/scale)^alpha))
    ∂characteristicKernel mu0 Phi (environment w)) ≤ 2 ↔ _
  rw [hid.1]
  rfl


/-- Markovness and the literal initial-law pushforward for the population
coefficient stored in a full history, derived from the raw causal maps. -/
theorem sourceFullHistoryPreLaw_properties
    (mu0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure mu0]
    (tau : ℕ -> ℝ)
    (flow : (n : ℕ) -> (Fin n -> W) -> ℝ -> EuclideanSpace ℝ (Fin d) -> EuclideanSpace ℝ (Fin d))
    (jump : (n : ℕ) -> (Fin n -> W) -> W -> EuclideanSpace ℝ (Fin d) -> EuclideanSpace ℝ (Fin d))
    (hflow : ∀ n t, Measurable (fun z : (Fin n -> W) × EuclideanSpace ℝ (Fin d) => flow n z.1 t z.2))
    (hjump : ∀ n, Measurable (fun z : ((Fin n -> W) × W) × EuclideanSpace ℝ (Fin d) => jump n z.1.1 z.1.2 z.2))
    (n : ℕ) :
    IsMarkovKernel (sourceFullHistoryPreLaw (Aux := Aux) mu0 tau flow jump n) ∧
      ∀ h : (Fin n -> W) × Aux,
        sourceFullHistoryPreLaw mu0 tau flow jump n h = mu0.map (sourceReferencePre tau flow jump n h.1) := by
  have hm : Measurable (fun z : ((Fin n -> W) × Aux) × EuclideanSpace ℝ (Fin d) =>
      sourceReferencePre tau flow jump n z.1.1 z.2) :=
    (sourceReferenceBranch_measurable tau flow jump hflow hjump n (tau (n+1))).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  exact characteristicKernel_properties mu0 _ hm

/-- A population-event moment bound implies prehistory eligibility using the
PROVED causal pre-law identity. The population event need not itself be
prehistory measurable, and the measure is never conditioned on that event. -/
theorem source_causal_population_event_implies_eligibility
    (mu0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure mu0]
    (tau : ℕ -> ℝ)
    (flow : (n : ℕ) -> (Fin n -> W) -> ℝ -> EuclideanSpace ℝ (Fin d) -> EuclideanSpace ℝ (Fin d))
    (jump : (n : ℕ) -> (Fin n -> W) -> W -> EuclideanSpace ℝ (Fin d) -> EuclideanSpace ℝ (Fin d))
    (hflow : ∀ n t, Measurable (fun z : (Fin n -> W) × EuclideanSpace ℝ (Fin d) => flow n z.1 t z.2))
    (hjump : ∀ n, Measurable (fun z : ((Fin n -> W) × W) × EuclideanSpace ℝ (Fin d) => jump n z.1.1 z.1.2 z.2))
    (n : ℕ) (environment : O -> Env) (past : Env -> Fin n -> W) (extra : O -> Aux)
    (alpha scale : ℝ) (Good : Set O)
    (hmoment : ∀ w ∈ Good,
      (∫⁻ x, ENNReal.ofReal (Real.exp ((‖x‖/scale)^alpha))
        ∂mu0.map (sourceReferencePre tau flow jump n (past (environment w)))) ≤ 2) :
    ∀ w ∈ Good, (past (environment w), extra w) ∈ populationExponentialEligibility
      (sourceFullHistoryPreLaw (Aux := Aux) mu0 tau flow jump n) alpha scale := by
  intro w hw
  change (∫⁻ x, ENNReal.ofReal (Real.exp ((‖x‖/scale)^alpha))
    ∂sourceFullHistoryPreLaw (Aux := Aux) mu0 tau flow jump n (past (environment w), extra w)) ≤ 2
  rw [(sourceFullHistoryPreLaw_properties (Aux := Aux) mu0 tau flow jump hflow hjump n).2]
  exact hmoment w hw

end PaperFormalization.Manuscript
