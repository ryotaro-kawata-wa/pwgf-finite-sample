import PaperFormalization.Manuscript.SourceCanonicalEmpiricalFlow
import PaperFormalization.Manuscript.SourceAuxiliaryCoordinates
import PaperFormalization.Manuscript.SourceFreshAuxiliaryHistories
import PaperFormalization.Manuscript.SourceRecurrentCoordinates
import Mathlib.MeasureTheory.Constructions.Pi

/-! # The original iid/auxiliary input law is invariant under block permutations
M13s verified unit; see CODEX_HANDOFF_M13S.md. Population innovations are kept fixed. The original sample and
every auxiliary normal are transformed together. Nothing is conditioned on a
localization or future event. The original underlying sample space need not
admit a pointwise permutation action; we use its exact pushforward input law.
-/
open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory
namespace PaperFormalization.Manuscript
variable {N d : Nat}

/-- Orthogonal reindexing preserves the standard Gaussian, including dimension zero. -/
theorem source_stdGaussian_isometry_invariant
    {I : Type*} [Fintype I] [DecidableEq I]
    (e : EuclideanSpace Real I ≃ₗᵢ[Real] EuclideanSpace Real I) :
    (stdGaussian (EuclideanSpace Real I)).map e = stdGaussian (EuclideanSpace Real I) := by
  apply Measure.ext_of_charFun
  funext x
  change charFun ((stdGaussian (EuclideanSpace Real I)).map (e : EuclideanSpace Real I →L[Real] EuclideanSpace Real I)) x = _
  simp only [charFun_map_clm_adjoint,LinearIsometryEquiv.adjoint_eq_symm,
    charFun_stdGaussian]
  change Complex.exp (-↑‖e.symm x‖ ^ 2 / 2) = Complex.exp (-↑‖x‖ ^ 2 / 2)
  rw [e.symm.norm_map]

/-- The permutation used by the fixed whitening rule has this exact marginal. -/
theorem source_step_normal_permutation (s : Equiv.Perm (Fin N)) :
    MeasurePreserving (sourceEuclideanPermute (sourceParticleIndexPermute (d := d) s))
      (stdGaussian (SourceStepNormal N d)) (stdGaussian (SourceStepNormal N d)) := by
  let e := LinearIsometryEquiv.piLpCongrLeft 2 Real Real (sourceParticleIndexPermute (d := d) s).symm
  exact ⟨e.continuous.measurable,source_stdGaussian_isometry_invariant e⟩

noncomputable def sourceInitialConfigurationLaw
    (mu0 : Measure (EuclideanSpace Real (Fin d))) : Measure (SourceFiniteConfiguration N d) :=
  (Measure.pi (fun _ : Fin N => mu0)).map (WithLp.toLp 2)

instance sourceInitialConfigurationLaw_probability
    (mu0 : Measure (EuclideanSpace Real (Fin d))) [IsProbabilityMeasure mu0] :
    IsProbabilityMeasure (sourceInitialConfigurationLaw (N := N) mu0) :=
  Measure.isProbabilityMeasure_map (WithLp.measurable_toLp 2 _).aemeasurable

theorem source_initial_configuration_permutation
    (mu0 : Measure (EuclideanSpace Real (Fin d))) [IsProbabilityMeasure mu0]
    (s : Equiv.Perm (Fin N)) :
    MeasurePreserving (sourceParticlePermute s) (sourceInitialConfigurationLaw (N := N) mu0)
      (sourceInitialConfigurationLaw (N := N) mu0) := by
  refine ⟨sourceParticlePermute_measurable s,?_⟩
  have hi : (Measure.pi (fun _ : Fin N => mu0)).map (fun x i => x (s i)) =
      Measure.pi (fun _ : Fin N => mu0) := by
    have he : (MeasurableEquiv.piCongrLeft (fun _ : Fin N => EuclideanSpace Real (Fin d)) s.symm :
        (Fin N -> EuclideanSpace Real (Fin d)) -> (Fin N -> EuclideanSpace Real (Fin d))) =
          (fun x i => x (s i)) := by
      funext x i
      simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    simpa only [he] using (measurePreserving_piCongrLeft (fun _ : Fin N => mu0) s.symm).map_eq
  have hm : Measurable (fun x : Fin N -> EuclideanSpace Real (Fin d) => fun i => x (s i)) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply (s i))
  calc
    _ = ((Measure.pi (fun _ : Fin N => mu0)).map (fun x i => x (s i))).map (WithLp.toLp 2) := by
      unfold sourceInitialConfigurationLaw
      rw [Measure.map_map (sourceParticlePermute_measurable s) (WithLp.measurable_toLp 2 _),
        Measure.map_map (WithLp.measurable_toLp 2 _) hm]
      rfl
    _ = _ := by rw [hi]; rfl

/-- The original population environment and initial cloud have the exact product
law. Array independence, not empirical-particle independence, is used. -/
theorem source_original_input_product_law
    {O S : Type*} [MeasurableSpace O] [MeasurableSpace S]
    (nu : Measure O) [IsProbabilityMeasure nu]
    (mu0 : Measure (EuclideanSpace Real (Fin d))) [IsProbabilityMeasure mu0]
    (env : O -> S) (initial : O -> SourceFiniteConfiguration N d)
    (henv : Measurable env) (hinit : Measurable initial)
    (hiid : iIndepFun (fun i o => initial o i) nu)
    (hind : IndepFun env (fun o i => initial o i) nu)
    (hlaw : forall i, nu.map (fun o => initial o i) = mu0) :
    nu.map (fun o => (env o,initial o)) =
      (nu.map env).prod (sourceInitialConfigurationLaw (N := N) mu0) := by
  have hm i : Measurable (fun o => initial o i) :=
    ((measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 _)).comp hinit
  have harray : nu.map (fun o i => initial o i) =
      Measure.pi (fun i => nu.map (fun o => initial o i)) :=
    hiid.map_fun_eq_pi_map (fun i => (hm i).aemeasurable)
  simp_rw [hlaw] at harray
  have hinitLaw : nu.map initial = sourceInitialConfigurationLaw (N := N) mu0 := by
    unfold sourceInitialConfigurationLaw
    rw [<- harray,Measure.map_map (WithLp.measurable_toLp 2 _) (measurable_pi_lambda _ hm)]
    rfl
  have hind' : IndepFun env initial nu := by
    simpa only [Function.comp_def,id_eq] using hind.comp measurable_id (WithLp.measurable_toLp 2 _)
  rw [hind'.map_prod_eq_prod_map_map henv.aemeasurable hinit.aemeasurable,hinitLaw]

/-- Map the original datum and all auxiliary coordinates by fixed maps. -/
def sourceAuxiliaryTransform {S A : Type*} (f : S -> S) (g : A -> A) :
    (n : Nat) -> SourceAuxiliarySpace S A n -> SourceAuxiliarySpace S A n
  | 0,z => ULift.up (f z.down)
  | n+1,z => (sourceAuxiliaryTransform f g n z.1,g z.2)

theorem sourceAuxiliaryTransform_measurable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (f : S -> S) (g : A -> A) (hf : Measurable f) (hg : Measurable g) (n : Nat) :
    Measurable (sourceAuxiliaryTransform f g n) := by
  induction n with
  | zero => exact measurable_up.comp (hf.comp measurable_down)
  | succ n ih => exact (ih.comp measurable_fst).prodMk (hg.comp measurable_snd)

theorem sourceAuxiliaryTransform_original {S A : Type*} (f : S -> S) (g : A -> A)
    (n : Nat) (z : SourceAuxiliarySpace S A n) :
    sourceAuxiliaryOriginal n (sourceAuxiliaryTransform f g n z) = f (sourceAuxiliaryOriginal n z) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih z.1

theorem sourceAuxiliaryTransform_array {S A : Type*} (f : S -> S) (g : A -> A)
    (n : Nat) (z : SourceAuxiliarySpace S A n) (i : Fin n) :
    sourceAuxiliaryArray n (sourceAuxiliaryTransform f g n z) i = g (sourceAuxiliaryArray n z i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun i => ?_) i
    . simp only [sourceAuxiliaryArray_last, sourceAuxiliaryTransform]
    . simpa only [sourceAuxiliaryTransform,sourceAuxiliaryArray_castSucc] using ih z.1 i

set_option backward.isDefEq.respectTransparency false in
/-- Product invariance is proved at every finite tower stage. -/
theorem sourceAuxiliaryTransform_preserving
    {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (rho : Measure S) [IsProbabilityMeasure rho] (lambda : Measure A) [IsProbabilityMeasure lambda]
    (f : S -> S) (g : A -> A) (hf : MeasurePreserving f rho rho)
    (hg : MeasurePreserving g lambda lambda) (n : Nat) :
    MeasurePreserving (sourceAuxiliaryTransform f g n)
      (sourceAuxiliaryMeasure rho lambda n) (sourceAuxiliaryMeasure rho lambda n) := by
  induction n with
  | zero =>
    refine ⟨sourceAuxiliaryTransform_measurable f g hf.measurable hg.measurable 0,?_⟩
    let e : SourceAuxiliarySpace S A 0 ≃ᵐ S := MeasurableEquiv.ulift
    apply e.map_measurableEquiv_injective
    rw [Measure.map_map e.measurable (sourceAuxiliaryTransform_measurable f g hf.measurable hg.measurable 0)]
    change (sourceAuxiliaryMeasure rho lambda 0).map (f ∘ sourceAuxiliaryOriginal 0) =
      (sourceAuxiliaryMeasure rho lambda 0).map (sourceAuxiliaryOriginal 0)
    rw [<- Measure.map_map hf.measurable (sourceAuxiliaryOriginal_preserving rho lambda 0).measurable,
      (sourceAuxiliaryOriginal_preserving rho lambda 0).map_eq,hf.map_eq]
  | succ n ih => exact ih.prod hg

set_option backward.isDefEq.respectTransparency false in
/-- The observation of original data on the tower has its exact pushed-forward
base law. This bridges arbitrary original sample spaces to the input-law proof. -/
theorem sourceAuxiliaryHistory_preserving
    {O S A : Type*} [MeasurableSpace O] [MeasurableSpace S] [MeasurableSpace A]
    (nu : Measure O) [IsProbabilityMeasure nu] (lambda : Measure A) [IsProbabilityMeasure lambda]
    (data : O -> S) (hdata : Measurable data) (n : Nat) :
    MeasurePreserving (sourceAuxiliaryHistory (A := A) data n)
      (sourceAuxiliaryMeasure nu lambda n) (sourceAuxiliaryMeasure (nu.map data) lambda n) := by
  letI : IsProbabilityMeasure (nu.map data) := Measure.isProbabilityMeasure_map hdata.aemeasurable
  induction n with
  | zero =>
    refine ⟨sourceAuxiliaryHistory_measurable data hdata 0,?_⟩
    let e : SourceAuxiliarySpace S A 0 ≃ᵐ S := MeasurableEquiv.ulift
    apply e.map_measurableEquiv_injective
    rw [Measure.map_map e.measurable (sourceAuxiliaryHistory_measurable data hdata 0)]
    change (sourceAuxiliaryMeasure nu lambda 0).map (data ∘ sourceAuxiliaryOriginal 0) =
      (sourceAuxiliaryMeasure (nu.map data) lambda 0).map (sourceAuxiliaryOriginal 0)
    rw [<- Measure.map_map hdata (sourceAuxiliaryOriginal_preserving nu lambda 0).measurable,
      (sourceAuxiliaryOriginal_preserving nu lambda 0).map_eq,
      (sourceAuxiliaryOriginal_preserving (nu.map data) lambda 0).map_eq]
  | succ n ih => exact ih.prod (MeasurePreserving.id lambda)

/-- Population coordinates are left fixed while the initial cloud is permuted. -/
def sourceInputPermute {S : Type*} (s : Equiv.Perm (Fin N))
    (z : S × SourceFiniteConfiguration N d) : S × SourceFiniteConfiguration N d :=
  (z.1,sourceParticlePermute s z.2)

theorem sourceInputPermute_preserving
    {O S : Type*} [MeasurableSpace O] [MeasurableSpace S]
    (nu : Measure O) [IsProbabilityMeasure nu]
    (mu0 : Measure (EuclideanSpace Real (Fin d))) [IsProbabilityMeasure mu0]
    (env : O -> S) (initial : O -> SourceFiniteConfiguration N d)
    (henv : Measurable env) (hinit : Measurable initial)
    (hiid : iIndepFun (fun i o => initial o i) nu)
    (hind : IndepFun env (fun o i => initial o i) nu)
    (hlaw : forall i, nu.map (fun o => initial o i) = mu0) (s : Equiv.Perm (Fin N)) :
    MeasurePreserving (sourceInputPermute s)
      (nu.map (fun o => (env o,initial o))) (nu.map (fun o => (env o,initial o))) := by
  letI : IsProbabilityMeasure (nu.map env) := Measure.isProbabilityMeasure_map henv.aemeasurable
  rw [source_original_input_product_law nu mu0 env initial henv hinit hiid hind hlaw]
  exact (MeasurePreserving.id _).prod (source_initial_configuration_permutation mu0 s)
end PaperFormalization.Manuscript
