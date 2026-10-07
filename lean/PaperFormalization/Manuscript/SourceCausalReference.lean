import PaperFormalization.Manuscript.SourceOriginalCovarianceView
import Mathlib.Tactic

/-! # The scheduled reference characteristic and its actual pre-law

M13p verified unit (see CODEX_HANDOFF_M13P.md). A branch flow at index n sees exactly the first n
population innovations; a jump sees that prefix and one new innovation. Initial
samples and whitening auxiliaries are not arguments of the common flow. The
finite recursion constructs the characteristic instead of assuming conditional
iid reference paths. Raw measurable flow and population-jump maps are the model
inputs; this module does not manufacture an ODE existence theorem.
-/
open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory
namespace PaperFormalization.Manuscript

variable {W E : Type*}

/-- Drop only the current innovation, retaining the ordered strict prefix. -/
def sourceHistoryInit {n : ℕ} (h : Fin (n+1) -> W) : Fin n -> W :=
  fun i => h i.castSucc

/-- Post-jump state at the beginning of branch n, built from n innovations. -/
def sourceReferencePost (tau : ℕ -> ℝ)
    (flow : (n : ℕ) -> (Fin n -> W) -> ℝ -> E -> E)
    (jump : (n : ℕ) -> (Fin n -> W) -> W -> E -> E) :
    (n : ℕ) -> (Fin n -> W) -> E -> E
  | 0, _, u => u
  | n+1, h, u => jump n (sourceHistoryInit h) (h (Fin.last n))
      (flow n (sourceHistoryInit h) (tau (n+1))
        (sourceReferencePost tau flow jump n (sourceHistoryInit h) u))

/-- A labelled closed branch. The endpoint before a jump remains on this branch. -/
def sourceReferenceBranch (tau : ℕ -> ℝ)
    (flow : (n : ℕ) -> (Fin n -> W) -> ℝ -> E -> E)
    (jump : (n : ℕ) -> (Fin n -> W) -> W -> E -> E)
    (n : ℕ) (h : Fin n -> W) (u : E) (t : ℝ) : E :=
  flow n h t (sourceReferencePost tau flow jump n h u)

/-- The population pre-jump characteristic, before innovation n is read. -/
def sourceReferencePre (tau : ℕ -> ℝ)
    (flow : (n : ℕ) -> (Fin n -> W) -> ℝ -> E -> E)
    (jump : (n : ℕ) -> (Fin n -> W) -> W -> E -> E)
    (n : ℕ) (h : Fin n -> W) (u : E) : E :=
  sourceReferenceBranch tau flow jump n h u (tau (n+1))

/-- The recursion is the prescribed population jump, not a whitened replacement. -/
theorem sourceReferencePost_succ (tau : ℕ -> ℝ)
    (flow : (n : ℕ) -> (Fin n -> W) -> ℝ -> E -> E)
    (jump : (n : ℕ) -> (Fin n -> W) -> W -> E -> E)
    (n : ℕ) (h : Fin (n+1) -> W) (u : E) :
    sourceReferencePost tau flow jump (n+1) h u =
      jump n (sourceHistoryInit h) (h (Fin.last n))
        (sourceReferencePre tau flow jump n (sourceHistoryInit h) u) := rfl

/-- Starting a flow at its own initial time identifies the right/post trace;
no equality between the two sides of a nonzero jump is imposed. -/
theorem sourceReferenceBranch_start (tau : ℕ -> ℝ)
    (flow : (n : ℕ) -> (Fin n -> W) -> ℝ -> E -> E)
    (jump : (n : ℕ) -> (Fin n -> W) -> W -> E -> E)
    (hstart : ∀ n h x, flow n h (tau n) x = x)
    (n : ℕ) (h : Fin n -> W) (u : E) :
    sourceReferenceBranch tau flow jump n h u (tau n) =
      sourceReferencePost tau flow jump n h u := hstart _ _ _

section Measurable
variable [MeasurableSpace W] [MeasurableSpace E]

theorem sourceHistoryInit_measurable (n : ℕ) :
    Measurable (sourceHistoryInit : (Fin (n+1) -> W) -> Fin n -> W) :=
  measurable_pi_lambda _ (fun i => measurable_pi_apply i.castSucc)

/-- Measurability of every characteristic is derived by finite composition of
raw flow and jump maps. No conditional-product conclusion is an input. -/
theorem sourceReferencePost_measurable (tau : ℕ -> ℝ)
    (flow : (n : ℕ) -> (Fin n -> W) -> ℝ -> E -> E)
    (jump : (n : ℕ) -> (Fin n -> W) -> W -> E -> E)
    (hflow : ∀ n t, Measurable (fun z : (Fin n -> W) × E => flow n z.1 t z.2))
    (hjump : ∀ n, Measurable (fun z : ((Fin n -> W) × W) × E =>
      jump n z.1.1 z.1.2 z.2)) (n : ℕ) :
    Measurable (fun z : (Fin n -> W) × E => sourceReferencePost tau flow jump n z.1 z.2) := by
  induction n with
  | zero => exact measurable_snd
  | succ n ih =>
    have hp : Measurable (fun z : (Fin (n+1) -> W) × E => sourceHistoryInit z.1) :=
      (sourceHistoryInit_measurable n).comp measurable_fst
    have hc : Measurable (fun z : (Fin (n+1) -> W) × E => z.1 (Fin.last n)) :=
      (measurable_pi_apply (Fin.last n)).comp measurable_fst
    exact (hjump n).comp ((hp.prodMk hc).prodMk
      ((hflow n (tau (n+1))).comp (hp.prodMk (ih.comp (hp.prodMk measurable_snd)))))

theorem sourceReferenceBranch_measurable (tau : ℕ -> ℝ)
    (flow : (n : ℕ) -> (Fin n -> W) -> ℝ -> E -> E)
    (jump : (n : ℕ) -> (Fin n -> W) -> W -> E -> E)
    (hflow : ∀ n t, Measurable (fun z : (Fin n -> W) × E => flow n z.1 t z.2))
    (hjump : ∀ n, Measurable (fun z : ((Fin n -> W) × W) × E =>
      jump n z.1.1 z.1.2 z.2)) (n : ℕ) (t : ℝ) :
    Measurable (fun z : (Fin n -> W) × E => sourceReferenceBranch tau flow jump n z.1 z.2 t) :=
  (hflow n t).comp (measurable_fst.prodMk (sourceReferencePost_measurable tau flow jump hflow hjump n))

/-- The law used as a coefficient in the full jump history. This is NOT the
conditional law of an observed particle given its own initial value. -/
noncomputable def sourceFullHistoryPreLaw {Aux : Type*} [MeasurableSpace Aux]
    (mu0 : Measure E) (tau : ℕ -> ℝ)
    (flow : (n : ℕ) -> (Fin n -> W) -> ℝ -> E -> E)
    (jump : (n : ℕ) -> (Fin n -> W) -> W -> E -> E) (n : ℕ) :
    Kernel ((Fin n -> W) × Aux) E :=
  characteristicKernel mu0 (fun h u => sourceReferencePre tau flow jump n h.1 u)

/-- The covariance history and the larger Gaussian history use exactly the
same population law. The equality is a consequence of the causal definitions,
not of uniqueness across two different conditioning sigma-fields. -/
theorem sourceCausalPreLaw_identity
    {Env Aux : Type*} [MeasurableSpace Env] [MeasurableSpace Aux]
    (mu0 : Measure E) [IsProbabilityMeasure mu0] (tau : ℕ -> ℝ)
    (flow : (n : ℕ) -> (Fin n -> W) -> ℝ -> E -> E)
    (jump : (n : ℕ) -> (Fin n -> W) -> W -> E -> E)
    (hflow : ∀ n t, Measurable (fun z : (Fin n -> W) × E => flow n z.1 t z.2))
    (hjump : ∀ n, Measurable (fun z : ((Fin n -> W) × W) × E =>
      jump n z.1.1 z.1.2 z.2)) (n : ℕ)
    (past : Env -> Fin n -> W) (hpast : Measurable past) (e : Env) (aux : Aux) :
    characteristicKernel mu0 (fun e u => sourceReferencePre tau flow jump n (past e) u) e =
      sourceFullHistoryPreLaw (Aux := Aux) mu0 tau flow jump n (past e, aux) ∧
    sourceFullHistoryPreLaw (Aux := Aux) mu0 tau flow jump n (past e, aux) =
      mu0.map (fun u => sourceReferenceBranch tau flow jump n (past e) u (tau (n+1))) := by
  have hpre := sourceReferenceBranch_measurable tau flow jump hflow hjump n (tau (n+1))
  have he : Measurable (fun z : Env × E => sourceReferencePre tau flow jump n (past z.1) z.2) :=
    hpre.comp ((hpast.comp measurable_fst).prodMk measurable_snd)
  have hh : Measurable (fun z : ((Fin n -> W) × Aux) × E =>
      sourceReferencePre tau flow jump n z.1.1 z.2) :=
    hpre.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have h1 := (characteristicKernel_properties mu0
    (fun e u => sourceReferencePre tau flow jump n (past e) u) he).2 e
  have h2 := (characteristicKernel_properties mu0
    (fun (h : (Fin n -> W) × Aux) u => sourceReferencePre tau flow jump n h.1 u) hh).2
    (past e, aux)
  exact ⟨h1.trans h2.symm, h2⟩

end Measurable
end PaperFormalization.Manuscript
