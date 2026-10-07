import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # MF29: signed time integrals and the label integral

Product-measure integrability on the full unordered closed time segment
supplies both iterated integrability statements before their interchange.
The formula includes equal and reversed endpoints.
-/
open MeasureTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Fubini for a signed time interval, with both genuine integrability outputs. -/
theorem signed_integral_fubini {A E : Type*} [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    (mu : Measure A) [SFinite mu] (f : Real → A → E) (s t : Real)
    (hf : Integrable (fun rw : Real × A => f rw.1 rw.2)
      ((volume.restrict (uIcc s t)).prod mu)) :
    IntervalIntegrable (fun r => ∫ w, f r w ∂mu) volume s t ∧
    Integrable (fun w => ∫ r in s..t, f r w) mu ∧
    (∫ w, (∫ r in s..t, f r w) ∂mu) = ∫ r in s..t, (∫ w, f r w ∂mu) := by
  have hst : Integrable (fun rw : Real × A => f rw.1 rw.2)
      ((volume.restrict (Ioc s t)).prod mu) :=
    hf.mono_measure (Measure.prod_mono
      (Measure.restrict_mono_set volume (Ioc_subset_uIoc.trans uIoc_subset_uIcc)) le_rfl)
  have hts : Integrable (fun rw : Real × A => f rw.1 rw.2)
      ((volume.restrict (Ioc t s)).prod mu) :=
    hf.mono_measure (Measure.prod_mono
      (Measure.restrict_mono_set volume (Ioc_subset_uIoc'.trans uIoc_subset_uIcc)) le_rfl)
  refine ⟨(intervalIntegrable_iff').mpr hf.integral_prod_left, ?_, ?_⟩
  · exact hst.integral_prod_right.sub hts.integral_prod_right
  · change (∫ w, ((∫ r in Ioc s t, f r w) - ∫ r in Ioc t s, f r w) ∂mu) = _
    rw [integral_sub hst.integral_prod_right hts.integral_prod_right,
      ← integral_integral_swap hst, ← integral_integral_swap hts]
    rfl

end PaperFormalization.MatrixFactorization
