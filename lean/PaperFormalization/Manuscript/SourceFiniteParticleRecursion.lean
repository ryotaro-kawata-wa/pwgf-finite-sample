import PaperFormalization.Manuscript.SourceCanonicalWhitening
import PaperFormalization.Manuscript.SourceCausalReference
import PaperFormalization.Manuscript.SourceParticleUnflatten

/-! # A finite causal population-first particle recursion

M13q verified unit (see CODEX_HANDOFF_M13Q.md). The empirical states are constructed, not
supplied as an already compatible view family. The finite coordinate is the
explicit canonical spectral-whitening formula. The reference always uses the
RAW field increment. By induction it is exactly the original one-seed causal
characteristic and retains its original conditional product law.

The deterministic recursion takes raw ODE solution maps and a measurable Gram
version. The source analytic units supply local empirical flows and the actual
Gram version. This file does not claim their global-horizon specialization or
all-stage stochastic whitening has already been assembled.
-/
open Matrix MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory
namespace PaperFormalization.Manuscript
attribute [local instance] sourceCanonicalMatrixMeasurable sourceCanonicalMatrixBorel

abbrev SourceFiniteConfiguration (N d : Nat) :=
  PiLp 2 (fun _ : Fin N => EuclideanSpace Real (Fin d))

/-- The population prefix omits all auxiliary coordinates pointwise. -/
def sourcePopulationPrefix {W A : Type*} {n : Nat} (h : Fin n -> W × A) : Fin n -> W :=
  fun i => (h i).1

theorem sourcePopulationPrefix_measurable {W A : Type*} [MeasurableSpace W] [MeasurableSpace A]
    (n : Nat) : Measurable (sourcePopulationPrefix : (Fin n -> W × A) -> Fin n -> W) :=
  measurable_pi_lambda _ (fun i => measurable_fst.comp (measurable_pi_apply i))

variable {N d : Nat} {W : Type*}

/-- The prescribed coupled jump with no probabilistic premise about its seed. -/
noncomputable def sourceCanonicalCoupledStep
    (M : SourceFiniteConfiguration N d -> Matrix (Fin N × Fin d) (Fin N × Fin d) Real)
    (hM : ∀ Y, (M Y).IsHermitian) (eta : Real)
    (C : Matrix (Fin N × Fin d) (Fin N × Fin d) Real)
    (X Y V : SourceFiniteConfiguration N d) (aux : EuclideanSpace Real (Fin N × Fin d)) :
    SourceFiniteConfiguration N d × SourceFiniteConfiguration N d :=
  (sourceParticleUnflatten (particleFlatten X + eta • matrixEuclideanOperator (M X)
    (sourceCanonicalWhiteningSeed (M Y) (hM Y) C (particleFlatten V) aux)), Y + eta • V)

/-- The empirical and reference post-jump states after n prescribed jumps.
The stored last innovation is never read while building the preceding state. -/
noncomputable def sourceCanonicalCoupledPost
    (tau eta : Nat -> Real)
    (flowX : Nat -> Real -> SourceFiniteConfiguration N d -> SourceFiniteConfiguration N d)
    (flowY : (n : Nat) -> (Fin n -> W) -> Real -> EuclideanSpace Real (Fin d) -> EuclideanSpace Real (Fin d))
    (field : (n : Nat) -> (Fin n -> W) -> W -> EuclideanSpace Real (Fin d) -> EuclideanSpace Real (Fin d))
    (M : SourceFiniteConfiguration N d -> Matrix (Fin N × Fin d) (Fin N × Fin d) Real)
    (hM : ∀ Y, (M Y).IsHermitian)
    (C : (n : Nat) -> (Fin n -> W) -> SourceFiniteConfiguration N d -> Matrix (Fin N × Fin d) (Fin N × Fin d) Real) :
    (n : Nat) -> (Fin n -> W × EuclideanSpace Real (Fin N × Fin d)) ->
      SourceFiniteConfiguration N d -> SourceFiniteConfiguration N d × SourceFiniteConfiguration N d
  | 0, _, u => (u,u)
  | n+1, h, u =>
    let past := sourceHistoryInit h
    let pop := sourcePopulationPrefix past
    let previous := sourceCanonicalCoupledPost tau eta flowX flowY field M hM C n past u
    let X := flowX n (tau (n+1)) previous.1
    let Y := WithLp.toLp 2 (fun i => flowY n pop (tau (n+1)) (previous.2 i))
    let V := WithLp.toLp 2 (fun i => field n pop (h (Fin.last n)).1 (Y i))
    sourceCanonicalCoupledStep M hM (eta n) (C n pop Y) X Y V (h (Fin.last n)).2

/-- No jumps preserve both initial configurations, including zero dimensions. -/
theorem sourceCanonicalCoupledPost_zero
    (tau eta : Nat -> Real) (flowX flowY field M hM C)
    (h : Fin 0 -> W × EuclideanSpace Real (Fin N × Fin d)) (u : SourceFiniteConfiguration N d) :
    sourceCanonicalCoupledPost tau eta flowX flowY field M hM C 0 h u = (u,u) := rfl

/-- The reference coordinate is EXACTLY the old causal characteristic, for
arbitrary auxiliary values. No measure, Gaussianity or independence is assumed. -/
theorem sourceCanonicalCoupledPost_reference
    (tau eta : Nat -> Real) (flowX flowY field M hM C)
    (n : Nat) (h : Fin n -> W × EuclideanSpace Real (Fin N × Fin d))
    (u : SourceFiniteConfiguration N d) (i : Fin N) :
    (sourceCanonicalCoupledPost tau eta flowX flowY field M hM C n h u).2 i =
      sourceReferencePost tau flowY
        (fun n pop w x => x + eta n • field n pop w x) n (sourcePopulationPrefix h) (u i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change flowY n (sourcePopulationPrefix (sourceHistoryInit h)) (tau (n+1))
        ((sourceCanonicalCoupledPost tau eta flowX flowY field M hM C n (sourceHistoryInit h) u).2 i) +
        eta n • field n (sourcePopulationPrefix (sourceHistoryInit h)) (h (Fin.last n)).1
          (flowY n (sourcePopulationPrefix (sourceHistoryInit h)) (tau (n+1))
            ((sourceCanonicalCoupledPost tau eta flowX flowY field M hM C n (sourceHistoryInit h) u).2 i)) = _
    rw [ih]
    rfl

section Measurable
variable [MeasurableSpace W]

/-- Finite causal composition establishes measurability of the constructed
particle pair. No measurable-selection premise is imposed on the output states. -/
theorem sourceCanonicalCoupledPost_measurable
    (tau eta : Nat -> Real) (flowX flowY field M hM C)
    (hFX : ∀ n t, Measurable (flowX n t))
    (hFY : ∀ n t, Measurable (fun z : (Fin n -> W) × EuclideanSpace Real (Fin d) => flowY n z.1 t z.2))
    (hField : ∀ n, Measurable (fun z : ((Fin n -> W) × W) × EuclideanSpace Real (Fin d) => field n z.1.1 z.1.2 z.2))
    (hMm : Measurable M)
    (hCm : ∀ n, Measurable (fun z : (Fin n -> W) × SourceFiniteConfiguration N d => C n z.1 z.2))
    (n : Nat) :
    Measurable (fun z : (Fin n -> W × EuclideanSpace Real (Fin N × Fin d)) × SourceFiniteConfiguration N d =>
      sourceCanonicalCoupledPost tau eta flowX flowY field M hM C n z.1 z.2) := by
  induction n with
  | zero => exact measurable_snd.prodMk measurable_snd
  | succ n ih =>
    let S := (Fin (n+1) -> W × EuclideanSpace Real (Fin N × Fin d)) × SourceFiniteConfiguration N d
    let past := fun z : S => sourceHistoryInit z.1
    let pop := fun z : S => sourcePopulationPrefix (past z)
    let prev := fun z : S => sourceCanonicalCoupledPost tau eta flowX flowY field M hM C n (past z) z.2
    let X := fun z : S => flowX n (tau (n+1)) (prev z).1
    let Y := fun z : S => WithLp.toLp 2 (fun i => flowY n (pop z) (tau (n+1)) ((prev z).2 i))
    let V := fun z : S => WithLp.toLp 2 (fun i => field n (pop z) (z.1 (Fin.last n)).1 (Y z i))
    let A := fun z : S => (z.1 (Fin.last n)).2
    have hpast : Measurable past := (sourceHistoryInit_measurable n).comp measurable_fst
    have hpop : Measurable pop := (sourcePopulationPrefix_measurable n).comp hpast
    have hprev : Measurable prev := ih.comp (hpast.prodMk measurable_snd)
    have hx : Measurable X := (hFX n (tau (n+1))).comp hprev.fst
    have hy : Measurable Y := by
      apply (WithLp.measurable_toLp 2 _).comp
      apply measurable_pi_lambda
      intro i
      have hcoord := ((measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 _)).comp hprev.snd
      exact (hFY n (tau (n+1))).comp (hpop.prodMk hcoord)
    have hw : Measurable (fun z : S => (z.1 (Fin.last n)).1) :=
      measurable_fst.comp ((measurable_pi_apply (Fin.last n)).comp measurable_fst)
    have ha : Measurable A := measurable_snd.comp ((measurable_pi_apply (Fin.last n)).comp measurable_fst)
    have hv : Measurable V := by
      apply (WithLp.measurable_toLp 2 _).comp
      apply measurable_pi_lambda
      intro i
      have hcoord := ((measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 _)).comp hy
      exact (hField n).comp ((hpop.prodMk hw).prodMk hcoord)
    have hc : Measurable (fun z : S => C n (pop z) (Y z)) := (hCm n).comp (hpop.prodMk hy)
    have hseed := (sourceCanonicalWhiteningSeed_measurable (fun z : S => M (Y z))
      (fun z => C n (pop z) (Y z)) (fun z => hM (Y z)) (hMm.comp hy) hc).comp
      (measurable_id.prodMk ((sourceParticleFlatten_measurable.comp hv).prodMk ha))
    have happ := measurable_matrix_euclidean_apply (fun z : S => M (X z))
      (fun z => sourceCanonicalWhiteningSeed (M (Y z)) (hM (Y z))
        (C n (pop z) (Y z)) (particleFlatten (V z)) (A z)) (hMm.comp hx) hseed
    have hxn := sourceParticleUnflatten_measurable.comp
      ((sourceParticleFlatten_measurable.comp hx).add (happ.const_smul (eta n)))
    have hyn := hy.add (hv.const_smul (eta n))
    simpa only [sourceCanonicalCoupledPost,sourceCanonicalCoupledStep,
      source_matrixEuclideanOperator_eq_toEuclideanCLM,Function.comp_def,
      Pi.add_apply, Pi.smul_apply, X, Y, V, A, prev, pop, past] using hxn.prodMk hyn

/-- The newly constructed finite reference array has its ORIGINAL conditional
product law. Auxiliary coordinates are not included in the conditioning map.
Thus the finite recursion does not silently change the reference system. -/
theorem sourceCanonicalCoupledPost_reference_joint_law
    {O : Type*} [MeasurableSpace O]
    (tau eta : Nat -> Real) (flowX flowY field M hM C)
    (hFY : ∀ n t, Measurable (fun z : (Fin n -> W) × EuclideanSpace Real (Fin d) => flowY n z.1 t z.2))
    (hField : ∀ n, Measurable (fun z : ((Fin n -> W) × W) × EuclideanSpace Real (Fin d) => field n z.1.1 z.1.2 z.2))
    (n : Nat) (nu : Measure O) [IsProbabilityMeasure nu]
    (mu0 : Measure (EuclideanSpace Real (Fin d))) [IsProbabilityMeasure mu0]
    (history : O -> Fin n -> W × EuclideanSpace Real (Fin N × Fin d))
    (initial : Fin N -> O -> EuclideanSpace Real (Fin d))
    (hH : Measurable history) (hinit : ∀ i, Measurable (initial i))
    (hiid : iIndepFun initial nu)
    (hind : IndepFun (sourcePopulationPrefix ∘ history) (fun o i => initial i o) nu)
    (hlaw : ∀ i, nu.map (initial i) = mu0) :
    let populationJump := fun n pop w x => x + eta n • field n pop w x
    let Phi := fun pop u => sourceReferencePost tau flowY populationJump n pop u
    nu.map (fun o => (sourcePopulationPrefix (history o),
      fun i => (sourceCanonicalCoupledPost tau eta flowX flowY field M hM C n (history o)
        (WithLp.toLp 2 (fun k => initial k o))).2 i)) =
      (nu.map (sourcePopulationPrefix ∘ history)) ⊗ₘ characteristicProductKernel (ι := Fin N) mu0 Phi := by
  let jump := fun n pop w x => x + eta n • field n pop w x
  have hjump : ∀ n, Measurable (fun z : ((Fin n -> W) × W) × EuclideanSpace Real (Fin d) => jump n z.1.1 z.1.2 z.2) :=
    fun n => measurable_snd.add ((hField n).const_smul (eta n))
  have hPhi := sourceReferencePost_measurable tau flowY jump hFY hjump n
  have hEnv := (sourcePopulationPrefix_measurable n).comp hH
  have h := independent_characteristic_joint_law nu mu0 (sourcePopulationPrefix ∘ history)
    initial hEnv hinit hiid hind hlaw (fun pop u => sourceReferencePost tau flowY jump n pop u) hPhi
  simpa only [sourceCanonicalCoupledPost_reference,Function.comp_def] using h
end Measurable
end PaperFormalization.Manuscript
