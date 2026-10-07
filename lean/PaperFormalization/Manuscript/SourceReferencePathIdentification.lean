import PaperFormalization.Manuscript.SourcePopulationPathSpace
import PaperFormalization.Manuscript.SourceCausalReference
import PaperFormalization.Manuscript.SourceReferencePathLaw

/-! # Causal reference paths and the reference component of the common path law

M13p verified unit (see CODEX_HANDOFF_M13P.md). Only the reference characteristic is a common
map of one initial seed. No such representation is asserted for empirical X.
The M13o pair-path observation still records actual X and Y separately.
-/
open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped Topology NNReal ProbabilityTheory
namespace PaperFormalization.Manuscript

abbrev SourceReferencePathSpace (J d : ℕ) (a b : Fin (J+1) -> ℝ) :=
  (j : Fin (J+1)) -> SourcePopulationBranchPath (a j) (b j) d

noncomputable def sourceReferencePathEval {J d : ℕ} {a b : Fin (J+1) -> ℝ}
    (path : SourceReferencePathSpace J d a b) (j : Fin (J+1)) (t : ℝ) :=
  sourcePopulationPathEval (fun _ : Fin 2 => path) 0 j t

theorem sourceReferencePathEval_measurable {J d : ℕ} {a b : Fin (J+1) -> ℝ}
    (j : Fin (J+1)) (t : ℝ) :
    Measurable (fun path : SourceReferencePathSpace J d a b => sourceReferencePathEval path j t) :=
  (sourcePopulationPathEval_measurable 0 j t).comp (measurable_pi_lambda _ (fun _ => measurable_id))

def sourceReferencePathLipschitz {J d : ℕ} {a b : Fin (J+1) -> ℝ} (B : ℝ≥0) :
    Set (SourceReferencePathSpace J d a b) :=
  (fun path => fun _ : Fin 2 => path) ⁻¹' sourcePopulationPathLipschitz B

theorem sourceReferencePathLipschitz_isClosed {J d : ℕ} {a b : Fin (J+1) -> ℝ} (B : ℝ≥0) :
    IsClosed (sourceReferencePathLipschitz (J := J) (d := d) (a := a) (b := b) B) :=
  (sourcePopulationPathLipschitz_isClosed B).preimage (continuous_pi (fun _ => continuous_id))

theorem sourceReferencePathLipschitz_iff {J d : ℕ} {a b : Fin (J+1) -> ℝ}
    (B : ℝ≥0) (path : SourceReferencePathSpace J d a b) :
    path ∈ sourceReferencePathLipschitz B ↔ ∀ j,
      LipschitzOnWith B (fun t => sourceReferencePathEval path j t) (Icc (a j) (b j)) := by
  change ((fun _ : Fin 2 => path) ∈ sourcePopulationPathLipschitz B) ↔ _
  rw [sourcePopulationPathLipschitz_iff]
  constructor
  · intro h j
    exact h 0 j
  · intro h c j
    exact h j

/-- All labelled evaluations of the M13o version identify the reference random
PATH outside one original-law null set. This discharges the path equality
premise used by original_reference_path_law_identified. -/
theorem source_reference_randomPath_eq_of_label_agreement
    {O Env Seed : Type*} [MeasurableSpace O] (nu : Measure O)
    {J d : ℕ} {a b : Fin (J+1) -> ℝ}
    (paths : O -> SourcePopulationPathSpace J d a b)
    (environment : O -> Env) (initial : O -> Seed)
    (Phi : Env -> Seed -> SourceReferencePathSpace J d a b)
    (raw : Env -> Seed -> Fin (J+1) -> ℝ -> EuclideanSpace ℝ (Fin d))
    (hversion : ∀ᵐ w ∂nu, ∀ j t, t ∈ Icc (a j) (b j) ->
      sourcePopulationPathEval (paths w) 1 j t = raw (environment w) (initial w) j t)
    (hPhi : ∀ᵐ w ∂nu, ∀ j t, t ∈ Icc (a j) (b j) ->
      sourceReferencePathEval (Phi (environment w) (initial w)) j t = raw (environment w) (initial w) j t) :
    (fun w => paths w 1) =ᵐ[nu] (fun w => Phi (environment w) (initial w)) := by
  filter_upwards [hversion, hPhi] with w hw hphi
  funext j
  apply ContinuousMap.ext
  intro t
  have heq := (hw j t t.property).trans (hphi j t t.property).symm
  simpa only [sourceReferencePathEval, sourcePopulationPathEval, dif_pos t.property] using heq

/-- Optional pointwise bundling for everywhere-continuous input branches.
The manuscript-level AE construction is exists_source_causal_reference_path_version;
it does not require this all-history hcont premise. -/
noncomputable def sourceCausalReferencePath
    {Env W : Type*} {J d : ℕ} (a b : Fin (J+1) -> ℝ)
    (tau : ℕ -> ℝ)
    (flow : (n : ℕ) -> (Fin n -> W) -> ℝ -> EuclideanSpace ℝ (Fin d) -> EuclideanSpace ℝ (Fin d))
    (jump : (n : ℕ) -> (Fin n -> W) -> W -> EuclideanSpace ℝ (Fin d) -> EuclideanSpace ℝ (Fin d))
    (past : (j : Fin (J+1)) -> Env -> Fin j.val -> W)
    (hcont : ∀ e u j, ContinuousOn (sourceReferenceBranch tau flow jump j.val (past j e) u) (Icc (a j) (b j)))
    (e : Env) (u : EuclideanSpace ℝ (Fin d)) : SourceReferencePathSpace J d a b :=
  fun j => ⟨fun t => sourceReferenceBranch tau flow jump j.val (past j e) u t, (hcont e u j).restrict⟩

theorem sourceCausalReferencePath_measurable
    {Env W : Type*} [MeasurableSpace Env] [MeasurableSpace W] {J d : ℕ}
    (a b : Fin (J+1) -> ℝ) (hab : ∀ j, a j ≤ b j) (tau : ℕ -> ℝ)
    (flow : (n : ℕ) -> (Fin n -> W) -> ℝ -> EuclideanSpace ℝ (Fin d) -> EuclideanSpace ℝ (Fin d))
    (jump : (n : ℕ) -> (Fin n -> W) -> W -> EuclideanSpace ℝ (Fin d) -> EuclideanSpace ℝ (Fin d))
    (hflow : ∀ n t, Measurable (fun z : (Fin n -> W) × EuclideanSpace ℝ (Fin d) => flow n z.1 t z.2))
    (hjump : ∀ n, Measurable (fun z : ((Fin n -> W) × W) × EuclideanSpace ℝ (Fin d) => jump n z.1.1 z.1.2 z.2))
    (past : (j : Fin (J+1)) -> Env -> Fin j.val -> W) (hpast : ∀ j, Measurable (past j))
    (hcont : ∀ e u j, ContinuousOn (sourceReferenceBranch tau flow jump j.val (past j e) u) (Icc (a j) (b j))) :
    Measurable (fun z : Env × EuclideanSpace ℝ (Fin d) => sourceCausalReferencePath a b tau flow jump past hcont z.1 z.2) := by
  apply measurable_pi_lambda
  intro j
  letI : Nonempty (Icc (a j) (b j)) := ⟨⟨a j, le_rfl, hab j⟩⟩
  apply sourcePopulationBranchPath_measurable_of_dense_evaluations (a j) (b j) d
    (denseSeq (Icc (a j) (b j))) (denseRange_denseSeq (Icc (a j) (b j)))
  intro n
  exact (sourceReferenceBranch_measurable tau flow jump hflow hjump j.val
    (denseSeq (Icc (a j) (b j)) n)).comp ((hpast j).comp measurable_fst |>.prodMk measurable_snd)

theorem sourceCausalReferencePath_eval
    {Env W : Type*} {J d : ℕ} (a b : Fin (J+1) -> ℝ) (tau : ℕ -> ℝ)
    (flow : (n : ℕ) -> (Fin n -> W) -> ℝ -> EuclideanSpace ℝ (Fin d) -> EuclideanSpace ℝ (Fin d))
    (jump : (n : ℕ) -> (Fin n -> W) -> W -> EuclideanSpace ℝ (Fin d) -> EuclideanSpace ℝ (Fin d))
    (past : (j : Fin (J+1)) -> Env -> Fin j.val -> W)
    (hcont : ∀ e u j, ContinuousOn (sourceReferenceBranch tau flow jump j.val (past j e) u) (Icc (a j) (b j)))
    (e : Env) (u : EuclideanSpace ℝ (Fin d)) (j : Fin (J+1)) (t : ℝ) (ht : t ∈ Icc (a j) (b j)) :
    sourceReferencePathEval (sourceCausalReferencePath a b tau flow jump past hcont e u) j t =
      sourceReferenceBranch tau flow jump j.val (past j e) u t := by
  simp only [sourceReferencePathEval, sourcePopulationPathEval, dif_pos ht,
    sourceCausalReferencePath, ContinuousMap.coe_mk]

end PaperFormalization.Manuscript
