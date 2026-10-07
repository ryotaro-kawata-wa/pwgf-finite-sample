import PaperFormalization.Manuscript.VarianceCosineCosineFlow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.Algebra.Order.Floor

/-! # The literal even-integer escape event implies the initial cosine gap
M13v VERIFIED UNIT (full example application remains open). The real infimum is used only after proving nonemptiness and
a lower bound. The closed countable intersection is measurable. The floor
argument covers all real landings, including negative and odd integers.
-/
open Set MeasureTheory
namespace PaperFormalization.Manuscript

def varianceCosineEscapeLanding (rho x : Real) : Prop :=
  forall k : Int, rho <= abs (x-2*(k : Real))

noncomputable def varianceCosineEvenDistance (x : Real) : Real :=
  sInf (Set.range (fun k : Int => abs (x-2*(k : Real))))

theorem varianceCosineEvenDistances_nonempty (x : Real) :
    (Set.range (fun k : Int => abs (x-2*(k : Real)))).Nonempty :=
  ⟨abs (x-2*(0 : Int)),0,rfl⟩

theorem varianceCosineEvenDistances_bddBelow (x : Real) :
    BddBelow (Set.range (fun k : Int => abs (x-2*(k : Real)))) := by
  refine ⟨0,?_⟩
  rintro y ⟨k,rfl⟩
  exact abs_nonneg _

theorem varianceCosineEscapeLanding_iff_distance (rho x : Real) :
    varianceCosineEscapeLanding rho x <-> rho <= varianceCosineEvenDistance x := by
  constructor
  . intro h
    apply le_csInf (varianceCosineEvenDistances_nonempty x)
    rintro y ⟨k,rfl⟩
    exact h k
  . intro h k
    exact h.trans (csInf_le (varianceCosineEvenDistances_bddBelow x) (mem_range_self k))

theorem varianceCosineEscapeLanding_measurable (rho : Real) :
    MeasurableSet {x : Real | varianceCosineEscapeLanding rho x} := by
  simp only [varianceCosineEscapeLanding,setOf_forall]
  apply MeasurableSet.iInter
  intro k
  exact measurableSet_le measurable_const (by fun_prop)

theorem varianceCosineEscapeLanding_bad_eq (rho : Real) :
    {x : Real | ¬ (varianceCosineEscapeLanding rho x)} =
      ⋃ k : Int, Ioo (2*(k : Real)-rho) (2*(k : Real)+rho) := by
  ext x
  simp only [mem_setOf_eq,varianceCosineEscapeLanding,not_forall,not_le,mem_iUnion,mem_Ioo]
  constructor
  . rintro ⟨k,h⟩
    refine ⟨k,?_⟩
    have hh := abs_lt.mp h
    constructor <;> linarith [hh.1,hh.2]
  . rintro ⟨k,h⟩
    refine ⟨k,abs_lt.mpr ?_⟩
    constructor <;> linarith [h.1,h.2]

/-- A nearest even integer exists by a floor construction, with no restriction
on the sign or magnitude of the landing. -/
theorem varianceCosine_nearest_even (x : Real) :
    exists k : Int, abs (x-2*(k : Real)) <= 1 := by
  let k := Int.floor ((x+1)/2)
  have hlo := Int.floor_le ((x+1)/2)
  have hhi := Int.lt_floor_add_one ((x+1)/2)
  refine ⟨k,abs_le.mpr ?_⟩
  constructor <;> dsimp [k] at * <;> linarith

theorem varianceCosineEvenDistance_mem (x : Real) :
    varianceCosineEvenDistance x ∈ Icc 0 1 := by
  constructor
  . apply le_csInf (varianceCosineEvenDistances_nonempty x)
    rintro y ⟨k,rfl⟩
    exact abs_nonneg _
  . obtain ⟨k,hk⟩ := varianceCosine_nearest_even x
    exact (csInf_le (varianceCosineEvenDistances_bddBelow x) (mem_range_self k)).trans hk

/-- Jordan's inequality on the nearest-even fundamental interval. -/
theorem varianceCosineEscapeLanding_gap (rho x : Real) (hr : 0 <= rho)
    (hx : varianceCosineEscapeLanding rho x) :
    2*rho^2 <= 1-Real.cos (Real.pi*x) := by
  obtain ⟨k,hk⟩ := varianceCosine_nearest_even x
  let r := x-2*(k : Real)
  have harg : abs (Real.pi*r) <= Real.pi := by
    rw [abs_mul,abs_of_pos Real.pi_pos]
    exact mul_le_of_le_one_right Real.pi_pos.le hk
  have hc := Real.cos_le_one_sub_mul_cos_sq harg
  have hcancel : 2/Real.pi^2*(Real.pi*r)^2 = 2*r^2 := by
    field_simp [Real.pi_ne_zero] <;> ring
  rw [hcancel] at hc
  have hperiod : Real.cos (Real.pi*r) = Real.cos (Real.pi*x) := by
    rw [show Real.pi*r = Real.pi*x-(k : Real)*(2*Real.pi) by dsimp [r]; ring]
    exact Real.cos_sub_int_mul_two_pi _ _
  rw [hperiod] at hc
  have hs : rho^2 <= r^2 := by
    have hsq := (sq_le_sq₀ hr (abs_nonneg r)).mpr (hx k)
    simpa only [sq_abs] using hsq
  linarith

/-- The original escape event, not a recovered-curvature premise, supplies the
cosine estimate needed on every later point of the used finite branch. -/
theorem varianceCosineMeanFlow_recovered_of_landing
    (beta T x rho t : Real) (hb : 0 < beta) (hr : 0 < rho)
    (hx : varianceCosineEscapeLanding rho x) (ht : t ∈ Icc 0 T)
    (hwait : varianceCosineRecoveryDelay (varianceCosineCurvatureScale beta) rho <= t) :
    Real.cos (Real.pi*varianceCosineMeanFlow beta T x t) <= -(1/2 : Real) :=
  varianceCosineMeanFlow_cosine_recovered beta T x rho t hb hr
    (varianceCosineEscapeLanding_gap rho x hr.le hx) ht hwait

theorem varianceCosineEscapeLanding_odd (rho : Real) (hr : rho <= 1) (k : Int) :
    varianceCosineEscapeLanding rho (2*(k : Real)+1) := by
  intro j
  have hne : 2*(k-j)+1 ≠ (0 : Int) := by omega
  have hInt : (1 : Int) <= abs (2*(k-j)+1) := Int.one_le_abs hne
  have hReal : (1 : Real) <= abs (2*((k : Real)-(j : Real))+1) := by exact_mod_cast hInt
  exact hr.trans (by convert hReal using 1 <;> congr 1 <;> ring)

theorem varianceCosineEscapeLanding_not_even (rho : Real) (hr : 0 < rho) (k : Int) :
    ¬ (varianceCosineEscapeLanding rho (2*(k : Real))) := by
  intro h
  have hk := h k
  simp only [sub_self,abs_zero] at hk
  linarith
end PaperFormalization.Manuscript
