import PaperFormalization.Manuscript.SourceOriginalObservationExtension
import PaperFormalization.Manuscript.SourceObservedJumpSchedule

/-! # A common finite auxiliary extension for all original-system observations

M13p verified unit (see CODEX_HANDOFF_M13P.md). A tower adds one fresh auxiliary coordinate per
step. Dropping future auxiliaries preserves each earlier law AND the original
coordinate. Previously constructed jump views can therefore be realized on the
same final space without new independence or observation-law assumptions.
This unit does not assert that a fresh GP stays Gaussian after revealing future
population fields; only independent AUXILIARY coordinates are dropped.
-/
open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory
namespace PaperFormalization.Manuscript
universe u v

/-- A concrete finite product extension. Level zero is a universe lift of the
original space; `sourceAuxiliaryOriginal` forgets that measurable equivalence.
This permits independent universe levels for the original and auxiliary spaces. -/
def SourceAuxiliarySpace (O : Type u) (A : Type v) : ℕ -> Type (max u v)
  | 0 => ULift.{v} O
  | n+1 => SourceAuxiliarySpace O A n × A

@[reducible] def sourceAuxiliaryMeasurable (O : Type u) (A : Type v)
    [MeasurableSpace O] [MeasurableSpace A] :
    (n : ℕ) -> MeasurableSpace (SourceAuxiliarySpace O A n)
  | 0 => inferInstanceAs (MeasurableSpace (ULift.{v} O))
  | n+1 => by
    letI := sourceAuxiliaryMeasurable O A n
    exact inferInstanceAs (MeasurableSpace (SourceAuxiliarySpace O A n × A))
attribute [instance] sourceAuxiliaryMeasurable

noncomputable def sourceAuxiliaryMeasure {O A : Type*} [MeasurableSpace O] [MeasurableSpace A]
    (nu : Measure O) (lambda : Measure A) : (n : ℕ) -> Measure (SourceAuxiliarySpace O A n)
  | 0 => nu.comap ULift.down
  | n+1 => (sourceAuxiliaryMeasure nu lambda n).prod lambda

instance sourceAuxiliaryMeasure_probability {O A : Type*} [MeasurableSpace O] [MeasurableSpace A]
    (nu : Measure O) [IsProbabilityMeasure nu] (lambda : Measure A) [IsProbabilityMeasure lambda]
    (n : ℕ) : IsProbabilityMeasure (sourceAuxiliaryMeasure nu lambda n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (nu.comap ULift.down))
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (IsProbabilityMeasure ((sourceAuxiliaryMeasure nu lambda n).prod lambda))

/-- Discard precisely the last m auxiliaries, never an original coordinate. -/
def sourceAuxiliaryProjection {O A : Type*} (n : ℕ) :
    (m : ℕ) -> SourceAuxiliarySpace O A (n+m) -> SourceAuxiliarySpace O A n
  | 0 => id
  | m+1 => fun z => sourceAuxiliaryProjection n m z.1

theorem sourceAuxiliaryProjection_preserving {O A : Type*} [MeasurableSpace O] [MeasurableSpace A]
    (nu : Measure O) [IsProbabilityMeasure nu] (lambda : Measure A) [IsProbabilityMeasure lambda]
    (n m : ℕ) :
    MeasurePreserving (sourceAuxiliaryProjection (O := O) (A := A) n m)
      (sourceAuxiliaryMeasure nu lambda (n+m)) (sourceAuxiliaryMeasure nu lambda n) := by
  induction m with
  | zero => exact MeasurePreserving.id _
  | succ m ih => exact ih.comp measurePreserving_fst

/-- Forget every auxiliary and the universe lift, retaining the original outcome. -/
def sourceAuxiliaryOriginal {O : Type u} {A : Type v} :
    (n : ℕ) → SourceAuxiliarySpace O A n → O
  | 0 => ULift.down
  | n+1 => fun z => sourceAuxiliaryOriginal n z.1

/-- The universe lift is a measurable equivalence, so every tower level has
exactly the original marginal under its original-coordinate projection. -/
theorem sourceAuxiliaryOriginal_preserving {O A : Type*}
    [MeasurableSpace O] [MeasurableSpace A]
    (nu : Measure O) [IsProbabilityMeasure nu]
    (lambda : Measure A) [IsProbabilityMeasure lambda] (n : ℕ) :
    MeasurePreserving (sourceAuxiliaryOriginal (O := O) (A := A) n)
      (sourceAuxiliaryMeasure nu lambda n) nu := by
  induction n with
  | zero =>
    let e : SourceAuxiliarySpace O A 0 ≃ᵐ O := MeasurableEquiv.ulift
    refine ⟨measurable_down, ?_⟩
    change (nu.comap e).map e = nu
    simpa using e.measurableEmbedding.map_comap nu
  | succ n ih => exact ih.comp measurePreserving_fst

/-- Earlier projections all retain the same original outcome pointwise. -/
theorem sourceAuxiliaryProjection_original {O A : Type*} (n m : ℕ)
    (z : SourceAuxiliarySpace O A (n+m)) :
    sourceAuxiliaryOriginal (O := O) (A := A) (n+m) z =
      sourceAuxiliaryOriginal (O := O) (A := A) n (sourceAuxiliaryProjection n m z) := by
  induction m with
  | zero => rfl
  | succ m ih => exact ih z.1

/-- An earlier level embeds observationally into any later one, with an exact
law and exact original-coordinate identity. This is an existence of a projection,
not a new stochastic coupling or conditional independence premise. -/
theorem exists_source_auxiliary_prefix {O A : Type*} [MeasurableSpace O] [MeasurableSpace A]
    (nu : Measure O) [IsProbabilityMeasure nu] (lambda : Measure A) [IsProbabilityMeasure lambda]
    (n J : ℕ) (hn : n ≤ J) :
    ∃ project : SourceAuxiliarySpace O A J -> SourceAuxiliarySpace O A n,
      MeasurePreserving project (sourceAuxiliaryMeasure nu lambda J) (sourceAuxiliaryMeasure nu lambda n) ∧
      ∀ z, sourceAuxiliaryOriginal (O := O) (A := A) J z = sourceAuxiliaryOriginal (O := O) (A := A) n (project z) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact ⟨sourceAuxiliaryProjection n m, sourceAuxiliaryProjection_preserving nu lambda n m,
    sourceAuxiliaryProjection_original n m⟩


/-- The original covariance observation is realized on the final tower by the
literal original-coordinate projection. Its iid law is never reconditioned. -/
noncomputable def sourceCovarianceView_on_auxiliaryTower
    {O A S V : Type*} [MeasurableSpace O] [MeasurableSpace A]
    [MeasurableSpace S] [MeasurableSpace V] {N d : ℕ} {alpha K : ℝ}
    (nu : Measure O) [IsProbabilityMeasure nu] (lambda : Measure A) [IsProbabilityMeasure lambda]
    (view : SourceObservedCovarianceView N d alpha K nu S V) :
    (J : ℕ) -> SourceObservedCovarianceView N d alpha K (sourceAuxiliaryMeasure nu lambda J) S V
  | 0 => {
      ρ := view.ρ, probability := view.probability
      k := view.k, markov := view.markov, κ := view.κ
      population_markov := view.population_markov
      PopGood := view.PopGood, measurable_popGood := view.measurable_popGood
      X := view.X, measurable_X := view.measurable_X, source_model := view.source_model
      observation := view.observation ∘ ULift.down
      measurable_observation := view.measurable_observation.comp measurable_down
      observation_law := by
        change (nu.comap ULift.down).map (view.observation ∘ ULift.down) = _
        rw [← Measure.map_map view.measurable_observation measurable_down]
        have hdown := (sourceAuxiliaryOriginal_preserving nu lambda 0).map_eq
        change (nu.comap (ULift.down : SourceAuxiliarySpace O A 0 → O)).map ULift.down = nu at hdown
        rw [hdown]
        exact view.observation_law }
  | J+1 => sourceCovarianceView_lift_auxiliary (sourceAuxiliaryMeasure nu lambda J) lambda
      (sourceCovarianceView_on_auxiliaryTower nu lambda view J)

theorem sourceCovarianceView_on_auxiliaryTower_observation
    {O A S V : Type*} [MeasurableSpace O] [MeasurableSpace A]
    [MeasurableSpace S] [MeasurableSpace V] {N d : ℕ} {alpha K : ℝ}
    (nu : Measure O) [IsProbabilityMeasure nu] (lambda : Measure A) [IsProbabilityMeasure lambda]
    (view : SourceObservedCovarianceView N d alpha K nu S V) (J : ℕ) :
    (sourceCovarianceView_on_auxiliaryTower nu lambda view J).observation =
      view.observation ∘ sourceAuxiliaryOriginal (O := O) (A := A) J := by
  induction J with
  | zero => rfl
  | succ J ih =>
    funext z
    exact congrFun ih z.1

section JumpPullback
variable {O O' S V : Type*} [MeasurableSpace O] [MeasurableSpace O']
  [MeasurableSpace S] [MeasurableSpace V] {N d : ℕ}
variable {H : ℕ -> Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]
variable {c p K D alpha : ℝ} {phi : ∀ n, EuclideanSpace ℝ (Fin d) -> H n}
  {G : lp H 2 -> ℝ} {U : Set (lp H 2)} {hU : IsOpen U}
  {hSU : measureMomentRegion (sourceWeightedFeatureMap c p phi) (sourceMomentClass alpha K) D ⊆ U}
  {hG : ContDiffOn ℝ 2 G U} {hN : 0 < N}

/-- Pull a constructed view to a common original extension. All conditional
kernels and primitive source-model facts are preserved, not reproved by a new
conditioning argument. This can be iterated along the finite auxiliary tower. -/
noncomputable def sourceJumpView_pullback {nu : Measure O} {nu' : Measure O'}
    (project : O' -> O) (hp : MeasurePreserving project nu' nu)
    (view : SourceObservedJumpView c p K D alpha phi G U hU hSU hG hN nu S V) :
    SourceObservedJumpView c p K D alpha phi G U hU hSU hG hN nu' S V := {
  ρ := view.ρ, probability := view.probability
  k := view.k, markov := view.markov, κ := view.κ
  PopGood := view.PopGood, measurable_popGood := view.measurable_popGood
  X := view.X, Y := view.Y, Xpost := view.Xpost, Ypost := view.Ypost
  measurable_X := view.measurable_X, measurable_Y := view.measurable_Y
  measurable_Xpost := view.measurable_Xpost, measurable_Ypost := view.measurable_Ypost
  seed := view.seed, eta := view.eta, eta_nonneg := view.eta_nonneg
  source_model := view.source_model
  observation := view.observation ∘ project
  measurable_observation := view.measurable_observation.comp hp.measurable
  observation_law := by
    rw [<- Measure.map_map view.measurable_observation hp.measurable, hp.map_eq]
    exact view.observation_law }

/-- Every step-level observed jump can be put on the SAME final auxiliary
space. No independence between these observations is needed for later unions.
The supplied stage views are obtained by exists_source_original_jump_view;
this theorem adds no new source_model or observation_law assumption. -/
theorem exists_source_jump_views_on_common_auxiliary_tower
    {A : Type*} [MeasurableSpace A] (nu : Measure O) [IsProbabilityMeasure nu]
    (lambda : Measure A) [IsProbabilityMeasure lambda] (J : ℕ)
    (S V : Fin J -> Type*) [∀ j, MeasurableSpace (S j)] [∀ j, MeasurableSpace (V j)]
    (views : ∀ j : Fin J, SourceObservedJumpView c p K D alpha phi G U hU hSU hG hN
      (sourceAuxiliaryMeasure nu lambda (j.val+1)) (S j) (V j)) :
    ∃ lifted : ∀ j : Fin J, SourceObservedJumpView c p K D alpha phi G U hU hSU hG hN
      (sourceAuxiliaryMeasure nu lambda J) (S j) (V j),
      ∀ j, ∃ project : SourceAuxiliarySpace O A J -> SourceAuxiliarySpace O A (j.val+1),
        MeasurePreserving project (sourceAuxiliaryMeasure nu lambda J) (sourceAuxiliaryMeasure nu lambda (j.val+1)) ∧
        (lifted j).observation = (views j).observation ∘ project ∧
        (lifted j).κ = (views j).κ ∧
        ∀ z, sourceAuxiliaryOriginal (O := O) (A := A) J z = sourceAuxiliaryOriginal (O := O) (A := A) (j.val+1) (project z) := by
  classical
  choose project hproject horiginal using fun j : Fin J =>
    exists_source_auxiliary_prefix nu lambda (j.val+1) J (Nat.succ_le_of_lt j.isLt)
  refine ⟨fun j => sourceJumpView_pullback (project j) (hproject j) (views j), ?_⟩
  intro j
  exact ⟨project j, hproject j, rfl, rfl, horiginal j⟩

end JumpPullback
end PaperFormalization.Manuscript
