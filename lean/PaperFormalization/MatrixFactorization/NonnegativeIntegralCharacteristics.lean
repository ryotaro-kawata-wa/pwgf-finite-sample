import PaperFormalization.MatrixFactorization.IntegralCharacteristicRegularity

/-! # MF28: assemble integral characteristics on the nonnegative time axis

Only the countable family of integer prefixes is intersected in the label
measure. Their integral equations yield local AC on every real segment and
the AE ODE on the whole time half-line. No uncountable family of conull label
sets is intersected. See `MF28_WORKLOG.md` for the verification state.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Integer closed prefixes exhaust nonnegative time. -/
theorem ae_nonnegative_of_ae_nat_prefix {P : Real → Prop}
    (hP : ∀ n : Nat, ∀ᵐ t ∂volume.restrict (Icc (0 : Real) n), P t) :
    ∀ᵐ t ∂volume.restrict (Ici (0 : Real)), P t := by
  apply (ae_restrict_iff' measurableSet_Ici).mpr
  have hall : ∀ᵐ t : Real, ∀ n : Nat, t ∈ Icc (0 : Real) n → P t := by
    apply ae_all_iff.mpr
    intro n
    exact (ae_restrict_iff' measurableSet_Icc).mp (hP n)
  filter_upwards [hall] with t ht hnonneg
  obtain ⟨n, hn⟩ := exists_nat_ge t
  exact ht n ⟨hnonneg, hn⟩

/-- Local integral equations imply AC on any signed nonnegative segment. -/
theorem integral_characteristic_ac_all_segments {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    {f v : Real → E}
    (hprefix : ∀ n : Nat, IntervalIntegrable v volume 0 n ∧
      ∀ t ∈ Icc (0 : Real) n, f t = f 0 - ∫ r in 0..t, v r)
    (s t : Real) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    AbsolutelyContinuousOnInterval f s t := by
  obtain ⟨n, hn⟩ := exists_nat_ge (max s t)
  have hsN : s ∈ uIcc (0 : Real) n := by
    rw [uIcc_of_le (Nat.cast_nonneg n)]
    exact ⟨hs, (le_max_left s t).trans hn⟩
  have htN : t ∈ uIcc (0 : Real) n := by
    rw [uIcc_of_le (Nat.cast_nonneg n)]
    exact ⟨ht, (le_max_right s t).trans hn⟩
  exact (integral_characteristic_ac (Nat.cast_nonneg n)
    (hprefix n).1 (hprefix n).2).mono (uIcc_subset_uIcc hsN htN)

theorem integral_characteristic_ae_ode_nonnegative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    {f v : Real → E}
    (hprefix : ∀ n : Nat, IntervalIntegrable v volume 0 n ∧
      ∀ t ∈ Icc (0 : Real) n, f t = f 0 - ∫ r in 0..t, v r) :
    ∀ᵐ t ∂volume.restrict (Ici (0 : Real)), HasDerivAt f (-v t) t := by
  apply ae_nonnegative_of_ae_nat_prefix
  intro n
  exact integral_characteristic_ae_ode (Nat.cast_nonneg n) (hprefix n).1 (hprefix n).2

/-- True prefix integrability and integral equations supply the exact label
and time quantifiers required by the existing AC characteristic class. -/
theorem ae_integral_characteristic_regular {A E : Type*} [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    (mu : Measure A) (f v : Real → A → E)
    (hprefix : ∀ n : Nat, ∀ᵐ w ∂mu,
      IntervalIntegrable (fun t => v t w) volume 0 n ∧
      ∀ t ∈ Icc (0 : Real) n, f t w = f 0 w - ∫ r in 0..t, v r w) :
    (∀ s t : Real, 0 ≤ s → 0 ≤ t → ∀ᵐ w ∂mu,
      AbsolutelyContinuousOnInterval (fun r => f r w) s t) ∧
    (∀ᵐ w ∂mu, ∀ᵐ t ∂volume.restrict (Ici (0 : Real)),
      HasDerivAt (fun r => f r w) (-v t w) t) := by
  have hall : ∀ᵐ w ∂mu, ∀ n : Nat,
      IntervalIntegrable (fun t => v t w) volume 0 n ∧
      ∀ t ∈ Icc (0 : Real) n, f t w = f 0 w - ∫ r in 0..t, v r w :=
    ae_all_iff.mpr hprefix
  constructor
  · intro s t hs ht
    filter_upwards [hall] with w hw
    exact integral_characteristic_ac_all_segments hw s t hs ht
  · filter_upwards [hall] with w hw
    exact integral_characteristic_ae_ode_nonnegative hw

end PaperFormalization.MatrixFactorization
