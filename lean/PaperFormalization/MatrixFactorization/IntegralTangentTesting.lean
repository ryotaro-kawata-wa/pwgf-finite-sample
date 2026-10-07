import PaperFormalization.MatrixFactorization.MeasurableExpTransport

/-! # MF24: L1-dual testing on the original, possibly atomic, sphere law

Verification status and conditional scope: see `MF24_VALIDATION.md`. A localized normalized tangent field tests the set where
a proposed representative exceeds a given norm bound. The resulting theorem
is measure-almost-everywhere, NOT everywhere on the closed support. The tangent
projection changes only an original null set. No volume Rademacher theorem,
density of the original measure, or unproved continuous-test density is used.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def excessTangentTest {d : Nat} (g : UnitSphere d → Weight d)
    (hg : Measurable g) (ht : ∀ w, inner Real w.val (g w) = 0)
    (C : Real) (hC : 0 ≤ C) : BoundedTangentTest d where
  field := fun w => if C < norm (g w) then (norm (g w))⁻¹ • g w else 0
  measurable_field := Measurable.ite (measurableSet_lt measurable_const hg.norm)
    (hg.norm.inv.smul hg) measurable_const
  tangent := by
    intro w
    split_ifs <;> simp only [real_inner_smul_right, ht, mul_zero, inner_zero_right]
  bound := 1
  bound_nonneg := zero_le_one
  norm_le := by
    intro w
    split_ifs with hh
    · have hn : 0 < norm (g w) := hC.trans_lt hh
      simp [norm_smul, Real.norm_eq_abs, abs_of_pos hn, hn.ne']
    · simp

/-- The normalized excess test realizes the positive part of norm(g)-C. -/
theorem excessTangentTest_pairing {d : Nat} (g : UnitSphere d → Weight d)
    (hg : Measurable g) (ht : ∀ w, inner Real w.val (g w) = 0)
    (C : Real) (hC : 0 ≤ C) (w : UnitSphere d) :
    inner Real (g w) ((excessTangentTest g hg ht C hC).field w) -
        C*norm ((excessTangentTest g hg ht C hC).field w) = max (norm (g w)-C) 0 := by
  by_cases hh : C < norm (g w)
  · have hn : 0 < norm (g w) := hC.trans_lt hh
    have hnorm : norm ((excessTangentTest g hg ht C hC).field w) = 1 := by
      simp [excessTangentTest, hh, norm_smul, Real.norm_eq_abs, abs_of_pos hn, hn.ne']
    rw [hnorm, mul_one, max_eq_left (sub_nonneg.mpr hh.le)]
    change inner Real (g w) (if C < norm (g w) then _ else _) - C = _
    rw [if_pos hh, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp [ne_of_gt hn]
    <;> ring
  · have hn : norm (g w)-C ≤ 0 := sub_nonpos.mpr (le_of_not_gt hh)
    simp only [excessTangentTest, if_neg hh, inner_zero_right, norm_zero,
      mul_zero, sub_self, max_eq_right hn]

/-- Upper bounds for ALL bounded Borel tangent tests imply the pointwise norm
bound almost everywhere with respect to the SAME original finite measure. -/
theorem ae_norm_le_of_bounded_tangent_tests {d : Nat} (mu : Measure (UnitSphere d))
    [IsFiniteMeasure mu] (g : UnitSphere d → Weight d)
    (hg : Measurable g) (hi : Integrable g mu)
    (ht : ∀ᵐ w ∂mu, inner Real w.val (g w) = 0)
    (C : Real) (hC : 0 ≤ C)
    (hbound : ∀ V : BoundedTangentTest d,
      (∫ w, inner Real (g w) (V.field w) ∂mu) ≤ C*(∫ w, norm (V.field w) ∂mu)) :
    ∀ᵐ w ∂mu, norm (g w) ≤ C := by
  let g0 := tangentVersion g
  have hm : Measurable g0 := tangentVersion_measurable g hg
  have htan : ∀ w, inner Real w.val (g0 w) = 0 := tangentVersion_tangent g
  have he : g0 =ᵐ[mu] g := tangentVersion_ae_eq mu g ht
  have hgi : Integrable g0 mu := tangentVersion_integrable mu g hi ht
  let V := excessTangentTest g0 hm htan C hC
  let F := fun w => max (norm (g0 w)-C) 0
  have hid : ∀ w, inner Real (g0 w) (V.field w)-C*norm (V.field w) = F w :=
    excessTangentTest_pairing g0 hm htan C hC
  have hpair := V.pairing_integrable mu g0 hgi
  have hvi := V.norm_integrable mu
  have hFi : Integrable F mu :=
    (hpair.sub (hvi.const_mul C)).congr (Eventually.of_forall hid)
  have hFeq : (∫ w, F w ∂mu) =
      (∫ w, inner Real (g0 w) (V.field w) ∂mu)-C*(∫ w, norm (V.field w) ∂mu) := by
    calc
      _ = ∫ w, inner Real (g0 w) (V.field w)-C*norm (V.field w) ∂mu :=
        integral_congr_ae (Eventually.of_forall (fun w => (hid w).symm))
      _ = _ := by rw [integral_sub hpair (hvi.const_mul C), integral_const_mul]
  have hpeq : (∫ w, inner Real (g0 w) (V.field w) ∂mu) =
      (∫ w, inner Real (g w) (V.field w) ∂mu) := by
    apply integral_congr_ae
    filter_upwards [he] with w hw
    rw [hw]
  have hFzero : (∫ w, F w ∂mu) = 0 := by
    apply le_antisymm
    · rw [hFeq, hpeq]
      linarith [hbound V]
    · exact integral_nonneg (fun w => le_max_right _ _)
  have hae := (integral_eq_zero_iff_of_nonneg (fun w => le_max_right (norm (g0 w)-C) 0)
    hFi).mp hFzero
  filter_upwards [hae, he] with w hw hgw
  have hh : norm (g0 w)-C ≤ max (norm (g0 w)-C) 0 := le_max_left _ _
  rw [hw, hgw] at hh
  exact sub_nonpos.mp hh

/-- Uniqueness is equality of L2 representatives almost everywhere, not an
unsupported claim that values on null subsets of the support are equal. -/
theorem ae_eq_of_bounded_tangent_pairings {d : Nat} (mu : Measure (UnitSphere d))
    [IsFiniteMeasure mu] (g k : UnitSphere d → Weight d)
    (hg : Measurable g) (hk : Measurable k) (hgi : Integrable g mu) (hki : Integrable k mu)
    (hgt : ∀ᵐ w ∂mu, inner Real w.val (g w) = 0)
    (hkt : ∀ᵐ w ∂mu, inner Real w.val (k w) = 0)
    (he : ∀ V : BoundedTangentTest d,
      (∫ w, inner Real (g w) (V.field w) ∂mu) =
        (∫ w, inner Real (k w) (V.field w) ∂mu)) : g =ᵐ[mu] k := by
  have htan : ∀ᵐ w ∂mu, inner Real w.val (g w-k w) = 0 := by
    filter_upwards [hgt, hkt] with w hw hk'
    simp only [inner_sub_right, hw, hk', sub_self]
  have hb := ae_norm_le_of_bounded_tangent_tests mu (fun w => g w-k w)
    (hg.sub hk) (hgi.sub hki) htan 0 le_rfl (by
      intro V
      simp only [inner_sub_left, zero_mul]
      rw [integral_sub (V.pairing_integrable mu g hgi) (V.pairing_integrable mu k hki), he V]
      simp)
  filter_upwards [hb] with w hw
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hw (norm_nonneg _)))

end PaperFormalization.MatrixFactorization
