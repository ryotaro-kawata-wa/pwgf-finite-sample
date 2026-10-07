import PaperFormalization.MatrixFactorization.NonnegativeIntegralCharacteristics
import PaperFormalization.MatrixFactorization.PrimalACCharacteristics

/-! # MF28: the same primal AC trajectory has an integral characteristic form

The integral equation is simultaneous in all nonnegative endpoints on one
conull set of original labels. It is obtained by intersecting integer-prefix
AC statements, not an uncountable collection of endpointwise AE identities.
This also checks the converse direction of the integral-to-AC bridge.
Execution status is recorded in `MF28_WORKLOG.md`.
-/
open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

/-- A whole integer prefix is handled on one conull set of original labels. -/
theorem PrimalACCharacteristicData.integral_prefix_ae
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (i : Fin 2) (n : Nat) :
    ∀ᵐ w ∂initial i,
      IntervalIntegrable (fun t => X.pullbackGradient i t w) volume 0 n ∧
      ∀ t ∈ Icc (0 : Real) n,
        (X.characteristic i t w).val = (X.characteristic i 0 w).val -
          ∫ r in 0..t, X.pullbackGradient i r w := by
  filter_upwards [X.speed_bound_ae hl hp i,
    X.path_ac i 0 n le_rfl (Nat.cast_nonneg n), X.ode i] with w hb hac hd
  have hv := intervalIntegrable_of_nonnegative_ae_bound
    (fun t => X.pullbackGradient i t w) (X.pullbackGradient_measurable_time i w)
    (primalObjectiveSpeedBound d O a lambda p) hb le_rfl (Nat.cast_nonneg n)
  refine ⟨hv, ?_⟩
  intro t ht
  have hsub : uIcc (0 : Real) t ⊆ uIcc (0 : Real) n := by
    apply uIcc_subset_uIcc (by simp)
    simpa only [uIcc_of_le (Nat.cast_nonneg n)] using ht
  have hder : ∀ᵐ r : Real, r ∈ uIcc (0 : Real) t →
      HasDerivAt (fun r => (X.characteristic i r w).val)
        (-X.pullbackGradient i r w) r :=
    ae_nonnegative_to_segment le_rfl ht.1 hd
  have he := integral_eq_sub_of_ac_ae_velocity (hac.mono hsub) (hv.mono_set hsub).neg hder
  simp only [Pi.neg_apply, intervalIntegral.integral_neg] at he
  have hh := sub_eq_iff_eq_add.mp he.symm
  exact hh.trans (by abel)

/-- All real time pairs are quantified after one countable intersection. -/
theorem PrimalACCharacteristicData.integral_equation_ae_all_times
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p) (i : Fin 2) :
    ∀ᵐ w ∂initial i, ∀ s t : Real, 0 ≤ s → 0 ≤ t →
      IntervalIntegrable (fun r => X.pullbackGradient i r w) volume s t ∧
      (X.characteristic i t w).val - (X.characteristic i s w).val =
        -(∫ r in s..t, X.pullbackGradient i r w) := by
  have hall : ∀ᵐ w ∂initial i, ∀ n : Nat,
      IntervalIntegrable (fun t => X.pullbackGradient i t w) volume 0 n ∧
      ∀ t ∈ Icc (0 : Real) n,
        (X.characteristic i t w).val = (X.characteristic i 0 w).val -
          ∫ r in 0..t, X.pullbackGradient i r w :=
    ae_all_iff.mpr (X.integral_prefix_ae hl hp i)
  filter_upwards [hall] with w hw
  intro s t hs ht
  obtain ⟨n, hn⟩ := exists_nat_ge (max s t)
  have hsN : s ∈ Icc (0 : Real) n := ⟨hs, (le_max_left s t).trans hn⟩
  have htN : t ∈ Icc (0 : Real) n := ⟨ht, (le_max_right s t).trans hn⟩
  have hsU : s ∈ uIcc (0 : Real) n := by simpa only [uIcc_of_le (Nat.cast_nonneg n)] using hsN
  have htU : t ∈ uIcc (0 : Real) n := by simpa only [uIcc_of_le (Nat.cast_nonneg n)] using htN
  have hzero : (0 : Real) ∈ uIcc (0 : Real) n := by simp
  have h0s := (hw n).1.mono_set (uIcc_subset_uIcc hzero hsU)
  have h0t := (hw n).1.mono_set (uIcc_subset_uIcc hzero htU)
  refine ⟨(hw n).1.mono_set (uIcc_subset_uIcc hsU htU), ?_⟩
  rw [(hw n).2 t htN, (hw n).2 s hsN]
  calc
    _ = -((∫ r in 0..t, X.pullbackGradient i r w) -
        ∫ r in 0..s, X.pullbackGradient i r w) := by abel
    _ = _ := congrArg Neg.neg (intervalIntegral.integral_interval_sub_left h0t h0s)

/-- The initial point is the original label, with true integrability and a
simultaneous nonnegative-time integral characteristic representation. -/
theorem PrimalACCharacteristicData.integral_from_initial_label_ae
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p) (i : Fin 2) :
    ∀ᵐ w ∂initial i, ∀ t : Real, 0 ≤ t →
      IntervalIntegrable (fun r => X.pullbackGradient i r w) volume 0 t ∧
      (X.characteristic i t w).val = w.val - ∫ r in 0..t, X.pullbackGradient i r w := by
  filter_upwards [X.integral_equation_ae_all_times hl hp i,
    Measure.support_mem_ae (μ := initial i)] with w hw hs
  intro t ht
  obtain ⟨hint, he⟩ := hw 0 t le_rfl ht
  rw [X.initial_map i w hs] at he
  refine ⟨hint, ?_⟩
  exact (sub_eq_iff_eq_add.mp he).trans (by abel)

end PaperFormalization.MatrixFactorization
