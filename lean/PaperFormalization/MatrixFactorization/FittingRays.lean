import PaperFormalization.MatrixFactorization.FittingEnergy

/-! # MF01: exact first/second derivatives at the fitting active origin

These are output-linear (equivalently, once the Hermite
coordinate bridge is supplied, ambient moment) rays. They are NOT asserted to
be admissible spherical pushforwards. Constructing such directions and proving
the teacher visibility condition are separate source obligations.
-/

open MeasureTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

variable {Omega : Type*} [MeasurableSpace Omega] {h : Nat}

/-- Differentiation of an exact polynomial, not interchange with a limit. -/
theorem fittingEnergy_ray_hasDerivAt (P : Measure Omega) (H : Omega -> Output h)
    (X Y : Omega -> Weight h)
    (hH : StronglyMeasurable H) (hX : StronglyMeasurable X) (hY : StronglyMeasurable Y)
    (hH2 : Integrable (fun z => norm (H z)^2) P)
    (hX4 : Integrable (fun z => norm (X z)^4) P)
    (hY4 : Integrable (fun z => norm (Y z)^4) P) (t : Real) :
    HasDerivAt (fun s : Real => fittingEnergy P H (fun z => s • X z) (fun z => s • Y z))
      (-2*t*integral P (fun z => inner Real (H z) (outer (X z) (Y z))) +
        2*t^3*integral P (fun z => norm (outer (X z) (Y z))^2)) t := by
  let C := integral P (fun z => inner Real (H z) (outer (X z) (Y z)))
  let Q := integral P (fun z => norm (outer (X z) (Y z))^2)
  let E0 := fittingEnergy P H (fun _ => 0) (fun _ => 0)
  have heq : (fun s : Real => fittingEnergy P H (fun z => s • X z) (fun z => s • Y z)) =
      fun s => E0-s^2*C+(s^4/2)*Q := by
    funext s
    exact fittingEnergy_ray_polynomial P H X Y hH hX hY hH2 hX4 hY4 s
  rw [heq]
  have hd := ((hasDerivAt_const t E0).sub (((hasDerivAt_id t).pow 2).mul_const C)).add
    ((((hasDerivAt_id t).pow 4).div_const 2).mul_const Q)
  convert hd using 1 <;> first
    | rfl
    | (dsimp [C,Q]; ring)

theorem fittingEnergy_ray_second (P : Measure Omega) (H : Omega -> Output h)
    (X Y : Omega -> Weight h)
    (hH : StronglyMeasurable H) (hX : StronglyMeasurable X) (hY : StronglyMeasurable Y)
    (hH2 : Integrable (fun z => norm (H z)^2) P)
    (hX4 : Integrable (fun z => norm (X z)^4) P)
    (hY4 : Integrable (fun z => norm (Y z)^4) P) (t : Real) :
    HasDerivAt
      (deriv (fun s : Real => fittingEnergy P H (fun z => s • X z) (fun z => s • Y z)))
      (-2*integral P (fun z => inner Real (H z) (outer (X z) (Y z))) +
        6*t^2*integral P (fun z => norm (outer (X z) (Y z))^2)) t := by
  let C := integral P (fun z => inner Real (H z) (outer (X z) (Y z)))
  let Q := integral P (fun z => norm (outer (X z) (Y z))^2)
  have heq : deriv (fun s : Real => fittingEnergy P H (fun z => s • X z) (fun z => s • Y z)) =
      fun s => -2*s*C+2*s^3*Q := by
    funext s
    exact (fittingEnergy_ray_hasDerivAt P H X Y hH hX hY hH2 hX4 hY4 s).deriv
  rw [heq]
  have hd := (((hasDerivAt_id t).const_mul (-2)).mul_const C).add
    ((((hasDerivAt_id t).pow 3).const_mul 2).mul_const Q)
  convert hd using 1 <;> first
    | rfl
    | (dsimp [C,Q]; ring)

/-- First fitting variation vanishes at the zero-output pair in every ray. -/
theorem fittingEnergy_origin_first (P : Measure Omega) (H : Omega -> Output h)
    (X Y : Omega -> Weight h)
    (hH : StronglyMeasurable H) (hX : StronglyMeasurable X) (hY : StronglyMeasurable Y)
    (hH2 : Integrable (fun z => norm (H z)^2) P)
    (hX4 : Integrable (fun z => norm (X z)^4) P)
    (hY4 : Integrable (fun z => norm (Y z)^4) P) :
    HasDerivAt (fun s : Real => fittingEnergy P H (fun z => s • X z) (fun z => s • Y z)) 0 0 := by
  simpa using fittingEnergy_ray_hasDerivAt P H X Y hH hX hY hH2 hX4 hY4 0

/-- The same-density direction has second derivative -2 times true visibility. -/
theorem fittingEnergy_same_density_second (P : Measure Omega) (teacher X : Omega -> Weight h)
    (ht : StronglyMeasurable teacher) (hX : StronglyMeasurable X)
    (ht4 : Integrable (fun z => norm (teacher z)^4) P)
    (hX4 : Integrable (fun z => norm (X z)^4) P) :
    HasDerivAt
      (deriv (fun s : Real => fittingEnergy P (fun z => outer (teacher z) (teacher z))
        (fun z => s • X z) (fun z => s • X z)))
      (-2*integral P (fun z => (inner Real (teacher z) (X z))^2)) 0 := by
  have hH := outer_stronglyMeasurable teacher teacher ht ht
  have hH2 := outer_sq_integrable P teacher teacher ht ht ht4 ht4
  simpa [outer_inner, pow_two] using
    fittingEnergy_ray_second P _ X X hH hX hX hH2 hX4 hX4 0

/-- The opposite direction has the positive sign, not the saddle descent sign. -/
theorem fittingEnergy_opposite_second (P : Measure Omega) (teacher X : Omega -> Weight h)
    (ht : StronglyMeasurable teacher) (hX : StronglyMeasurable X)
    (ht4 : Integrable (fun z => norm (teacher z)^4) P)
    (hX4 : Integrable (fun z => norm (X z)^4) P) :
    HasDerivAt
      (deriv (fun s : Real => fittingEnergy P (fun z => outer (teacher z) (teacher z))
        (fun z => s • X z) (fun z => s • (-X z))))
      (2*integral P (fun z => (inner Real (teacher z) (X z))^2)) 0 := by
  have hH := outer_stronglyMeasurable teacher teacher ht ht
  have hH2 := outer_sq_integrable P teacher teacher ht ht ht4 ht4
  have hn4 : Integrable (fun z => norm (-X z)^4) P := by simpa only [norm_neg] using hX4
  simpa [outer_neg_right, inner_neg_right, outer_inner, pow_two, integral_neg] using
    fittingEnergy_ray_second P _ X (fun z => -X z) hH hX hX.neg hH2 hX4 hn4 0

/-- A genuine algebraic descent criterion. The visibility assumption here is
explicit; no source teacher-imbalance theorem is claimed to have supplied it. -/
theorem fittingEnergy_visible_ray_descent (P : Measure Omega) (H : Omega -> Output h)
    (X Y : Omega -> Weight h)
    (hH : StronglyMeasurable H) (hX : StronglyMeasurable X) (hY : StronglyMeasurable Y)
    (hH2 : Integrable (fun z => norm (H z)^2) P)
    (hX4 : Integrable (fun z => norm (X z)^4) P)
    (hY4 : Integrable (fun z => norm (Y z)^4) P)
    (hVisible : 0 < integral P (fun z => inner Real (H z) (outer (X z) (Y z)))) :
    ∃ r : Real, 0<r ∧ forall t : Real, 0<abs t -> abs t<r ->
      fittingEnergy P H (fun z => t • X z) (fun z => t • Y z) <
        fittingEnergy P H (fun _ => 0) (fun _ => 0) := by
  let C := integral P (fun z => inner Real (H z) (outer (X z) (Y z)))
  let Q := integral P (fun z => norm (outer (X z) (Y z))^2)
  have hC : 0<C := hVisible
  have hQ : 0<=Q := integral_nonneg (fun _ => sq_nonneg _)
  refine .intro (min 1 (C/(Q+1))) (.intro (lt_min (by norm_num) (by positivity)) ?_)
  intro t ht0 ht
  have ht1 : abs t<1 := ht.trans_le (min_le_left _ _)
  have htc : abs t<C/(Q+1) := ht.trans_le (min_le_right _ _)
  have htc' : abs t*(Q+1)<C := (lt_div_iff₀ (by linarith : 0<Q+1)).mp htc
  have ht2 : t^2<=abs t := by nlinarith [sq_abs t]
  have htpos : 0<t^2 := by nlinarith [sq_abs t]
  have hq : t^2*Q<C := by nlinarith
  have hneg : t^2*(-C+t^2*Q/2)<0 := mul_neg_of_pos_of_neg htpos (by linarith)
  rw [fittingEnergy_ray_polynomial P H X Y hH hX hY hH2 hX4 hY4 t]
  change _ - t^2*C+(t^4/2)*Q < _
  nlinarith

end PaperFormalization.MatrixFactorization
