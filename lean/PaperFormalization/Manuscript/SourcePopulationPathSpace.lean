import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import PaperFormalization.Manuscript.OriginalPopulationEvent
import Mathlib.Tactic

/-! # A standard Borel space for the two labelled closed population paths

M13o declarations checked with the pinned toolchain; see verification/latest.json.
Each branch has its own closed-interval continuous path. Adjacent endpoint labels
are deliberately not identified, and a singleton final branch is allowed.
A fixed countable dense sequence is deterministic encoding data, not a sample
localization or probabilistic independence assumption. The measurable version
below changes all coordinates together on one null set under the original law.
-/
open MeasureTheory Set TopologicalSpace
open scoped Topology NNReal
namespace PaperFormalization.Manuscript

/-- One closed continuous branch, including the singleton-interval case. -/
abbrev SourcePopulationBranchPath (a b : ℝ) (d : ℕ) :=
  C(Icc a b, EuclideanSpace ℝ (Fin d))

noncomputable instance sourcePopulationBranchPathMeasurableSpace (a b : ℝ) (d : ℕ) :
    MeasurableSpace (SourcePopulationBranchPath a b d) := borel _

instance sourcePopulationBranchPathBorelSpace (a b : ℝ) (d : ℕ) :
    BorelSpace (SourcePopulationBranchPath a b d) := ⟨rfl⟩

/-- The compact-domain continuous-map topology is complete and separable. -/
theorem sourcePopulationBranchPath_standardBorel (a b : ℝ) (d : ℕ) :
    StandardBorelSpace (SourcePopulationBranchPath a b d) := by
  infer_instance

instance sourcePopulationBranchPathStandardBorel (a b : ℝ) (d : ℕ) :
    StandardBorelSpace (SourcePopulationBranchPath a b d) :=
  sourcePopulationBranchPath_standardBorel a b d

/-- Two populations and every closed branch are encoded by a single random element. -/
abbrev SourcePopulationPathSpace (J d : ℕ) (a b : Fin (J+1) → ℝ) :=
  Fin 2 → (j : Fin (J+1)) → SourcePopulationBranchPath (a j) (b j) d

theorem sourcePopulationPathSpace_standardBorel
    (J d : ℕ) (a b : Fin (J+1) → ℝ) :
    StandardBorelSpace (SourcePopulationPathSpace J d a b) := by infer_instance

/-- Evaluation is extended by zero outside its own closed branch. This convention
is used only to have a total map; all source conclusions are restricted to the branch. -/
noncomputable def sourcePopulationPathEval {J d : ℕ} {a b : Fin (J+1) → ℝ}
    (path : SourcePopulationPathSpace J d a b) (c : Fin 2) (j : Fin (J+1))
    (t : ℝ) : EuclideanSpace ℝ (Fin d) :=
  if ht : t ∈ Icc (a j) (b j) then path c j ⟨t,ht⟩ else 0

theorem sourcePopulationPathEval_measurable {J d : ℕ} {a b : Fin (J+1) → ℝ}
    (c : Fin 2) (j : Fin (J+1)) (t : ℝ) :
    Measurable (fun path : SourcePopulationPathSpace J d a b =>
      sourcePopulationPathEval path c j t) := by
  classical
  by_cases ht : t ∈ Icc (a j) (b j)
  · simpa only [sourcePopulationPathEval, dif_pos ht, Function.comp_def] using
      (continuous_eval_const (F := SourcePopulationBranchPath (a j) (b j) d) (⟨t,ht⟩ : Icc (a j) (b j))).measurable.comp
        ((measurable_pi_apply j).comp (measurable_pi_apply c))
  · simpa only [sourcePopulationPathEval, dif_neg ht] using
      (measurable_const : Measurable (fun _ : SourcePopulationPathSpace J d a b =>
        (0 : EuclideanSpace ℝ (Fin d))))

theorem sourcePopulationPathEval_endpoints {J d : ℕ} {a b : Fin (J+1) → ℝ}
    (path : SourcePopulationPathSpace J d a b) (c : Fin 2) (j : Fin (J+1))
    (hab : a j ≤ b j) :
    sourcePopulationPathEval path c j (a j) = path c j ⟨a j, le_rfl, hab⟩ ∧
    sourcePopulationPathEval path c j (b j) = path c j ⟨b j, hab, le_rfl⟩ := by
  simp [sourcePopulationPathEval, hab]

/-- Countably many dense evaluations determine a closed continuous branch and
its Borel measurability. The dense sequence is fixed independently of the sample. -/
theorem sourcePopulationBranchPath_measurable_of_dense_evaluations
    {O : Type*} [MeasurableSpace O] (a b : ℝ) (d : ℕ)
    (grid : ℕ → Icc a b) (hgrid : DenseRange grid)
    (paths : O → SourcePopulationBranchPath a b d)
    (hEval : ∀ n, Measurable (fun x => paths x (grid n))) : Measurable paths := by
  let code := fun f : SourcePopulationBranchPath a b d => fun n : ℕ => f (grid n)
  have hcode : Continuous code := continuous_pi fun n =>
    continuous_eval_const (F := SourcePopulationBranchPath a b d) (grid n)
  have hinj : Function.Injective code := by
    intro f g hfg
    apply ContinuousMap.ext
    intro t
    have hsub : range grid ⊆ {s | f s = g s} := by
      rintro _ ⟨n,rfl⟩
      exact congrFun hfg n
    exact (closure_minimal hsub (isClosed_eq f.continuous g.continuous)) (hgrid t)
  have hemb : MeasurableEmbedding code := hcode.measurableEmbedding hinj
  apply hemb.measurable_comp_iff.mp
  exact measurable_pi_lambda _ hEval

/-- Encode actual continuous branches without imposing cross-jump continuity. -/
noncomputable def sourcePopulationPathEncode {J d : ℕ} {a b : Fin (J+1) → ℝ}
    (Z : Fin 2 → Fin (J+1) → ℝ → EuclideanSpace ℝ (Fin d))
    (hCont : ∀ c j, ContinuousOn (Z c j) (Icc (a j) (b j))) :
    SourcePopulationPathSpace J d a b :=
  fun c j => ⟨fun t => Z c j t, (hCont c j).restrict⟩

theorem sourcePopulationPathEncode_eval {J d : ℕ} {a b : Fin (J+1) → ℝ}
    (Z : Fin 2 → Fin (J+1) → ℝ → EuclideanSpace ℝ (Fin d))
    (hCont : ∀ c j, ContinuousOn (Z c j) (Icc (a j) (b j)))
    (c : Fin 2) (j : Fin (J+1)) (t : ℝ) (ht : t ∈ Icc (a j) (b j)) :
    sourcePopulationPathEval (sourcePopulationPathEncode Z hCont) c j t = Z c j t := by
  simp only [sourcePopulationPathEval, dif_pos ht, sourcePopulationPathEncode,
    ContinuousMap.coe_mk]

theorem sourcePopulationPathEncode_measurable
    {O : Type*} [MeasurableSpace O] {J d : ℕ} {a b : Fin (J+1) → ℝ}
    (grid : ∀ j, ℕ → Icc (a j) (b j)) (hgrid : ∀ j, DenseRange (grid j))
    (Z : Fin 2 → Fin (J+1) → O → ℝ → EuclideanSpace ℝ (Fin d))
    (hZ : ∀ c j t, Measurable (fun x => Z c j x t))
    (hCont : ∀ x c j, ContinuousOn (Z c j x) (Icc (a j) (b j))) :
    Measurable (fun x => sourcePopulationPathEncode (fun c j => Z c j x) (hCont x)) := by
  apply measurable_pi_lambda
  intro c
  apply measurable_pi_lambda
  intro j
  apply sourcePopulationBranchPath_measurable_of_dense_evaluations
    (a j) (b j) d (grid j) (hgrid j)
  intro n
  exact hZ c j (grid j n)

/-- A simultaneous measurable continuous-path version under the unchanged original
measure, derived from pointwise measurability and one AE branch-Lipschitz model.
The agreement is AE for ALL branch times together, not separately for each time. -/
theorem exists_source_population_path_version_of_dense_grids
    {O : Type*} [MeasurableSpace O] (nu : Measure O) {J d : ℕ}
    (a b : Fin (J+1) → ℝ) (B : ℝ≥0)
    (grid : ∀ j, ℕ → Icc (a j) (b j)) (hgrid : ∀ j, DenseRange (grid j))
    (Z : Fin 2 → Fin (J+1) → O → ℝ → EuclideanSpace ℝ (Fin d))
    (hZ : ∀ c j t, Measurable (fun x => Z c j x t))
    (hLip : ∀ᵐ x ∂nu, ∀ c j, LipschitzOnWith B (Z c j x) (Icc (a j) (b j))) :
    ∃ paths : O → SourcePopulationPathSpace J d a b, Measurable paths ∧
      ∀ᵐ x ∂nu, ∀ c j t, t ∈ Icc (a j) (b j) →
        sourcePopulationPathEval (paths x) c j t = Z c j x t := by
  classical
  obtain ⟨Bad, hBadSub, hBadMeas, hBadZero⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hLip)
  let Z' := fun c j x t => if x ∈ Bad then (0 : EuclideanSpace ℝ (Fin d)) else Z c j x t
  have hGood (x : O) (hx : x ∉ Bad) :
      ∀ c j, LipschitzOnWith B (Z c j x) (Icc (a j) (b j)) := by
    by_contra hn
    exact hx (hBadSub hn)
  have hCont : ∀ x c j, ContinuousOn (Z' c j x) (Icc (a j) (b j)) := by
    intro x c j
    by_cases hx : x ∈ Bad
    · simpa only [Z', if_pos hx] using
        (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : EuclideanSpace ℝ (Fin d))) _)
    · simpa only [Z', if_neg hx] using (hGood x hx c j).continuousOn
  have hZ' : ∀ c j t, Measurable (fun x => Z' c j x t) := by
    intro c j t
    exact Measurable.ite hBadMeas measurable_const (hZ c j t)
  let paths := fun x => sourcePopulationPathEncode (fun c j => Z' c j x) (hCont x)
  refine ⟨paths, sourcePopulationPathEncode_measurable grid hgrid Z' hZ' hCont, ?_⟩
  have hnot : ∀ᵐ x ∂nu, x ∉ Bad := by
    apply ae_iff.mpr
    simpa using hBadZero
  filter_upwards [hnot] with x hx
  intro c j t ht
  simpa only [paths, Z', if_neg hx] using
    sourcePopulationPathEncode_eval (fun c j => Z' c j x) (hCont x) c j t ht

/-- The branchwise B-Lipschitz support is expressed with closed distance inequalities. -/
def sourcePopulationPathLipschitz {J d : ℕ} {a b : Fin (J+1) → ℝ}
    (B : ℝ≥0) : Set (SourcePopulationPathSpace J d a b) :=
  {path | ∀ (c : Fin 2) (j : Fin (J+1)) (s t : Icc (a j) (b j)),
    dist (path c j s) (path c j t) ≤ (B : ℝ) * dist s t}

theorem sourcePopulationPathLipschitz_isClosed
    {J d : ℕ} {a b : Fin (J+1) → ℝ} (B : ℝ≥0) :
    IsClosed (sourcePopulationPathLipschitz (J := J) (d := d) (a := a) (b := b) B) := by
  simp only [sourcePopulationPathLipschitz, setOf_forall]
  apply isClosed_iInter
  intro c
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro s
  apply isClosed_iInter
  intro t
  have hs : Continuous (fun path : SourcePopulationPathSpace J d a b => path c j s) :=
    (continuous_eval_const (F := SourcePopulationBranchPath (a j) (b j) d) s).comp ((continuous_apply j).comp (continuous_apply c))
  have ht : Continuous (fun path : SourcePopulationPathSpace J d a b => path c j t) :=
    (continuous_eval_const (F := SourcePopulationBranchPath (a j) (b j) d) t).comp ((continuous_apply j).comp (continuous_apply c))
  exact isClosed_le (hs.dist ht) continuous_const

theorem sourcePopulationPathLipschitz_iff
    {J d : ℕ} {a b : Fin (J+1) → ℝ} (B : ℝ≥0)
    (path : SourcePopulationPathSpace J d a b) :
    path ∈ sourcePopulationPathLipschitz B ↔
      ∀ c j, LipschitzOnWith B (fun t => sourcePopulationPathEval path c j t)
        (Icc (a j) (b j)) := by
  constructor
  · intro hp c j
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    simpa only [sourcePopulationPathEval, dif_pos hs, dif_pos ht, Subtype.dist_eq] using
      hp c j ⟨s,hs⟩ ⟨t,ht⟩
  · intro hp c j s t
    simpa only [sourcePopulationPathEval, dif_pos s.property, dif_pos t.property,
      Subtype.dist_eq] using
      (hp c j).dist_le_mul s s.property t t.property

/-- The fixed dense sequences are constructed from closed-interval separability.
The caller supplies no extra grid or positive interval-length assumption. -/
theorem exists_source_population_path_version
    {O : Type*} [MeasurableSpace O] (nu : Measure O) {J d : ℕ}
    (a b : Fin (J+1) → ℝ) (B : ℝ≥0) (hab : ∀ j, a j ≤ b j)
    (Z : Fin 2 → Fin (J+1) → O → ℝ → EuclideanSpace ℝ (Fin d))
    (hZ : ∀ c j t, Measurable (fun x => Z c j x t))
    (hLip : ∀ᵐ x ∂nu, ∀ c j, LipschitzOnWith B (Z c j x) (Icc (a j) (b j))) :
    ∃ paths : O → SourcePopulationPathSpace J d a b, Measurable paths ∧
      ∀ᵐ x ∂nu, ∀ c j t, t ∈ Icc (a j) (b j) →
        sourcePopulationPathEval (paths x) c j t = Z c j x t := by
  letI : ∀ j, Nonempty (Icc (a j) (b j)) :=
    fun j => ⟨⟨a j, le_rfl, hab j⟩⟩
  exact exists_source_population_path_version_of_dense_grids nu a b B
    (fun j => denseSeq (Icc (a j) (b j))) (fun j => denseRange_denseSeq (Icc (a j) (b j)))
    Z hZ hLip
end PaperFormalization.Manuscript
