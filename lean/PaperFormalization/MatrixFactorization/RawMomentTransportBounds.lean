import PaperFormalization.MatrixFactorization.SphericalTransportContinuity
import PaperFormalization.MatrixFactorization.SphereMoments

/-! # MF23: raw tensor coordinates are angular-Lipschitz on the sphere

Execution records: `MF23_VALIDATION.md`.

The bound is proved for the original full finite tensor
coordinates, including order zero. No injectivity of a finite moment map is
claimed. The coordinate Lipschitz constant is n, independent of the measures.
The existing all-coupling expectation estimate supplies genuine integrability.
-/
open MeasureTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- A finite product of real factors in the closed unit ball stays in that ball. -/
theorem real_unit_product_norm_le {ι : Type*} (s : Finset ι) (x : ι → Real)
    (hx : ∀ j ∈ s, norm (x j) ≤ 1) : norm (s.prod x) ≤ 1 := by
  classical
  revert hx
  induction s using Finset.induction_on with
  | empty => intro hx; simp
  | @insert j s hj ih =>
    intro hx
    have hxj := hx j (Finset.mem_insert_self j s)
    have hxs := ih (fun k hk => hx k (Finset.mem_insert_of_mem hk))
    rw [Finset.prod_insert hj,norm_mul]
    nlinarith [norm_nonneg (x j),norm_nonneg (s.prod x)]

/-- A telescoping estimate retaining the zero-cardinality case. -/
theorem real_unit_product_difference {ι : Type*} (s : Finset ι) (x y : ι → Real)
    (C : Real) (hC : 0 ≤ C)
    (hx : ∀ j ∈ s, norm (x j) ≤ 1) (hy : ∀ j ∈ s, norm (y j) ≤ 1)
    (hxy : ∀ j ∈ s, norm (x j-y j) ≤ C) :
    norm (s.prod x-s.prod y) ≤ (s.card : Real)*C := by
  classical
  revert hx hy hxy
  induction s using Finset.induction_on with
  | empty => intro hx hy hxy; simp
  | @insert j s hj ih =>
    intro hx hy hxy
    have hxj := hx j (Finset.mem_insert_self j s)
    have hdj := hxy j (Finset.mem_insert_self j s)
    have hys : ∀ k ∈ s, norm (y k) ≤ 1 := fun k hk => hy k (Finset.mem_insert_of_mem hk)
    have hpys := real_unit_product_norm_le s y hys
    have hd := ih (fun k hk => hx k (Finset.mem_insert_of_mem hk)) hys
      (fun k hk => hxy k (Finset.mem_insert_of_mem hk))
    rw [Finset.prod_insert hj,Finset.prod_insert hj]
    calc
      norm (x j*s.prod x-y j*s.prod y) =
          norm (x j*(s.prod x-s.prod y)+(x j-y j)*s.prod y) := by congr 1; ring
      _ ≤ norm (x j*(s.prod x-s.prod y))+norm ((x j-y j)*s.prod y) := norm_add_le _ _
      _ = norm (x j)*norm (s.prod x-s.prod y)+norm (x j-y j)*norm (s.prod y) := by
        rw [norm_mul,norm_mul]
      _ ≤ 1*((s.card : Real)*C)+C*1 :=
        add_le_add (mul_le_mul hxj hd (norm_nonneg _) zero_le_one)
          (mul_le_mul hdj hpys (norm_nonneg _) hC)
      _ = ((insert j s).card : Real)*C := by
        rw [Finset.card_insert_of_notMem hj]
        push_cast
        ring

/-- Every full coordinate of w tensor-power n has angular Lipschitz constant n. -/
theorem tensorCoordinate_spherical_lipschitz {d n : Nat} (I : Fin n → Fin d)
    (w y : UnitSphere d) :
    norm (tensorPower n w.val I-tensorPower n y.val I) ≤ (n : Real)*sphericalDistance w y := by
  have hcoord (z : UnitSphere d) (j : Fin n) : norm (z.val (I j)) ≤ 1 := by
    simpa only [unitSphere_norm] using PiLp.norm_apply_le z.val (I j)
  have hdiff (j : Fin n) : norm (w.val (I j)-y.val (I j)) ≤ sphericalDistance w y := by
    have hh : norm (w.val (I j)-y.val (I j)) ≤ norm (w.val-y.val) := by
      simpa only [PiLp.sub_apply] using PiLp.norm_apply_le (w.val-y.val) (I j)
    exact hh.trans (unitSphere_chord_le_sphericalDistance w y)
  have hh := real_unit_product_difference Finset.univ (fun j : Fin n => w.val (I j))
    (fun j : Fin n => y.val (I j)) (sphericalDistance w y) (sphericalDistance_nonneg w y)
    (fun j _ => hcoord w j) (fun j _ => hcoord y j) (fun j _ => hdiff j)
  simpa only [tensorPower_apply,Finset.card_univ,Fintype.card_fin] using hh

/-- Coordinate evaluation commutes with the genuine Bochner moment integral. -/
theorem rawMoment_apply_integral {d n : Nat} (mu : Measure (UnitSphere d))
    [IsFiniteMeasure mu] (I : Fin n → Fin d) :
    rawMoment mu n I = ∫ w, tensorPower n w.val I ∂mu := by
  change (PiLp.proj (𝕜 := Real) 2 (fun _ : Fin n → Fin d => Real) I)
    (integral mu (fun w => tensorPower n w.val)) = _
  exact ((PiLp.proj (𝕜 := Real) 2 (fun _ : Fin n → Fin d => Real) I).integral_comp_comm
    (rawMoment_integrable mu n)).symm

/-- This estimate is for original moments and the true infimum over all couplings. -/
theorem rawMoment_coordinate_transport_bound {d n : Nat}
    (mu nu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (I : Fin n → Fin d) :
    norm (rawMoment mu n I-rawMoment nu n I) ≤
      (n : Real)*Real.sqrt (sphericalWassersteinSq mu nu) := by
  rw [rawMoment_apply_integral mu I,rawMoment_apply_integral nu I]
  apply sphericalWasserstein_expectation_sub_norm_le mu nu
    (fun w => tensorPower n w.val I) _ (n : Real) (by positivity)
    (tensorCoordinate_spherical_lipschitz I)
  unfold tensorPower
  fun_prop

end PaperFormalization.MatrixFactorization
