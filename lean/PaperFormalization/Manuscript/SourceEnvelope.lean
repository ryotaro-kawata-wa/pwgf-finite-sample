import PaperFormalization.Manuscript.JumpForcing
import PaperFormalization.Manuscript.EnvelopeSupremum

/-! # The actual source envelope supremum and its zero case

The source eta-response is represented exactly by the generic curvature
envelope with majorized additive jumps. Its real supremum is justified by
boundedness rather than assumed continuity or attainment. A zero supremum
forces the actual source jump errors to vanish when all scheduled jumps lie
within the horizon. Pre-jump residual bounds remain explicit deterministic
inputs; no probability or conditional-law claim is made.
-/

open MeasureTheory Set
open scoped BigOperators

namespace PaperFormalization.Manuscript

open Continuous

/-- The manuscript's whole-horizon supremum of its eta-response envelope. -/
noncomputable def sourceCurvatureEnvelopeSup (kappa : ℝ → ℝ) (tau eta : ℕ → ℝ)
    (delta deltaTilde A : ℝ) (L : ℕ) (T : ℝ) : ℝ :=
  curvatureEnvelopeSup kappa tau
    (fun i => A * (Real.sqrt delta + Real.sqrt deltaTilde) * eta i) delta L T

/-- This is literally the supremum of the source-envelope values on [0,T]. -/
theorem sourceCurvatureEnvelopeSup_eq_sSup (kappa : ℝ → ℝ) (tau eta : ℕ → ℝ)
    (delta deltaTilde A : ℝ) (L : ℕ) (T : ℝ) :
    sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A L T =
      sSup ((sourceCurvatureEnvelope kappa tau eta delta deltaTilde A L) '' Icc 0 T) := by
  unfold sourceCurvatureEnvelopeSup curvatureEnvelopeSup curvatureEnvelopeValues
  congr 2
  funext t
  exact (sourceCurvatureEnvelope_eq_curvatureEnvelope kappa tau eta delta deltaTilde A L t).symm

/-- Every observed source response is below its actual finite real supremum. -/
theorem sourceCurvatureEnvelope_le_sup (kappa : ℝ → ℝ) (tau eta : ℕ → ℝ)
    (delta deltaTilde A : ℝ) (L : ℕ) (t T : ℝ)
    (hdelta : 0 ≤ delta) (hA : 0 ≤ A)
    (hkappa : IntervalIntegrable kappa volume 0 T)
    (htau : ∀ i < L, 0 ≤ tau (i + 1)) (heta : ∀ i < L, 0 ≤ eta i)
    (ht : t ∈ Icc 0 T) :
    sourceCurvatureEnvelope kappa tau eta delta deltaTilde A L t ≤
      sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A L T := by
  have hb : ∀ i < L, 0 ≤ A * (Real.sqrt delta + Real.sqrt deltaTilde) * eta i := by
    intro i hi
    exact mul_nonneg
      (mul_nonneg hA (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))) (heta i hi)
  rw [sourceCurvatureEnvelope_eq_curvatureEnvelope]
  exact curvatureEnvelope_le_sup kappa tau _ delta L t T
    (curvatureEnvelopeValues_bddAbove kappa tau _ delta L T hdelta hkappa htau hb) ht

/-- The finite source supremum is nonnegative, including at a zero-length horizon. -/
theorem sourceCurvatureEnvelopeSup_nonneg (kappa : ℝ → ℝ) (tau eta : ℕ → ℝ)
    (delta deltaTilde A : ℝ) (L : ℕ) (T : ℝ)
    (hT : 0 ≤ T) (hdelta : 0 ≤ delta) (hA : 0 ≤ A)
    (hkappa : IntervalIntegrable kappa volume 0 T)
    (htau : ∀ i < L, 0 ≤ tau (i + 1)) (heta : ∀ i < L, 0 ≤ eta i) :
    0 ≤ sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A L T :=
  (sourceCurvatureEnvelope_nonneg kappa tau eta delta deltaTilde A L 0
    hdelta hA le_rfl heta).trans
    (sourceCurvatureEnvelope_le_sup kappa tau eta delta deltaTilde A L 0 T
      hdelta hA hkappa htau heta ⟨le_rfl, hT⟩)

/-- A zero source supremum on a positive horizon makes delta and every actual
source jump forcing zero. All jumps must belong to this horizon. -/
theorem zero_forcing_of_zero_source_sup
    (kappa : ℝ → ℝ) (tau eta gammaPre gammaTildePre : ℕ → ℝ)
    (delta deltaTilde A : ℝ) (L : ℕ) (T : ℝ)
    (hT : 0 < T) (hdelta : 0 ≤ delta) (hA : 0 ≤ A)
    (hkappa : IntervalIntegrable kappa volume 0 T)
    (htau : ∀ i < L, 0 ≤ tau (i + 1)) (htauT : ∀ i < L, tau (i + 1) ≤ T)
    (heta : ∀ i < L, 0 ≤ eta i)
    (hgamma : ∀ i < L, gammaPre i ≤ delta)
    (hgammaTilde : ∀ i < L, gammaTildePre i ≤ deltaTilde)
    (hzero : sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A L T = 0) :
    delta = 0 ∧ ∀ i < L, sourceJumpForcing A eta gammaPre gammaTildePre i = 0 := by
  classical
  have hsource := sourceCurvatureEnvelope_le_sup kappa tau eta delta deltaTilde A L T T
    hdelta hA hkappa htau heta ⟨hT.le, le_rfl⟩
  rw [hzero] at hsource
  have hactual := (curvatureEnvelope_sourceJumpForcing_le kappa tau eta gammaPre gammaTildePre
    delta deltaTilde A L T hA heta hgamma hgammaTilde).trans hsource
  have hfilter : (Finset.range L).filter (fun i => tau (i + 1) ≤ T) = Finset.range L := by
    apply Finset.filter_eq_self.mpr
    intro i hi
    exact htauT i (Finset.mem_range.mp hi)
  have hactual' : delta * (∫ s in (0 : ℝ)..T, propagator kappa T s) +
      ∑ i ∈ Finset.range L, propagator kappa T (tau (i + 1)) *
        sourceJumpForcing A eta gammaPre gammaTildePre i ≤ 0 := by
    simpa only [curvatureEnvelope, hfilter] using hactual
  exact zero_forcing_of_zero_envelope kappa tau (sourceJumpForcing A eta gammaPre gammaTildePre)
    L T delta hT hdelta hkappa
    (fun i hi => sourceJumpForcing_nonneg A eta gammaPre gammaTildePre i hA (heta i hi)) hactual'

end PaperFormalization.Manuscript
