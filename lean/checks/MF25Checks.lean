import PaperFormalization.MatrixFactorization.PrimalACRegularityClosure

/-! MF25 boundary/API diagnostics. See `MF25_VALIDATION.md` for executed checks.
The examples exercise the signed FTC, zero speed and time, source objects,
AE quantifiers and the exact assembled endpoint. They are not numeric tests. -/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

-- 01: continuous linear observations of AC paths.
example {d : Nat} {f : Real → Weight d} {s t : Real}
    (L : Weight d →L[Real] Real) (hf : AbsolutelyContinuousOnInterval f s t) :
    AbsolutelyContinuousOnInterval (fun r => L (f r)) s t :=
  ac_comp_continuousLinearMap L hf

-- 02: full vector FTC, including d=0, without coordinate norm loss.
example {d : Nat} {f v : Real → Weight d} {s t : Real}
    (hf : AbsolutelyContinuousOnInterval f s t) (hv : IntervalIntegrable v volume s t)
    (hd : ∀ᵐ r, r ∈ uIcc s t → HasDerivAt f (v r) r) :
    (∫ r in s..t, v r) = f t - f s :=
  weight_integral_eq_sub_of_ac_ae_deriv hf hv hd

-- 03: restriction from the nonnegative half-line.
example {P : Real → Prop} {t : Real} (ht : 0 ≤ t)
    (hp : ∀ᵐ r ∂volume.restrict (Ici (0 : Real)), P r) :
    ∀ᵐ r, r ∈ uIcc 0 t → P r :=
  ae_nonnegative_to_segment le_rfl ht hp

-- 04: the negative-gradient sign.
example {d : Nat} (f v : Real → Weight d) (hv : Measurable v) (M s t : Real)
    (hb : ∀ᵐ r ∂volume.restrict (Ici (0 : Real)), norm (v r) ≤ M)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hac : AbsolutelyContinuousOnInterval f s t)
    (hd : ∀ᵐ r ∂volume.restrict (Ici (0 : Real)), HasDerivAt f (-v r) r) :
    f t - f s = -(∫ r in s..t, v r) :=
  (ac_negative_gradient_integral f v hv M hb hs ht hac hd).2

-- 05: endpoint distance with the SAME M.
example {d : Nat} (f v : Real → Weight d) (hv : Measurable v) (M s t : Real)
    (hb : ∀ᵐ r ∂volume.restrict (Ici (0 : Real)), norm (v r) ≤ M)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hac : AbsolutelyContinuousOnInterval f s t)
    (hd : ∀ᵐ r ∂volume.restrict (Ici (0 : Real)), HasDerivAt f (-v r) r) :
    dist (f s) (f t) ≤ M * dist s t :=
  ac_negative_gradient_endpoint_bound f v hv M hb hs ht hac hd

-- 06: a zero-length interval does not require an endpoint derivative.
example {d : Nat} (v : Real → Weight d) (s : Real) :
    (∫ r in s..s, v r) = 0 := by simp

-- 07: reversed endpoints use the signed integral and AC symmetry.
example {d : Nat} (f v : Real → Weight d) (hv : Measurable v) (M s t : Real)
    (hb : ∀ᵐ r ∂volume.restrict (Ici (0 : Real)), norm (v r) ≤ M)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hac : AbsolutelyContinuousOnInterval f s t)
    (hd : ∀ᵐ r ∂volume.restrict (Ici (0 : Real)), HasDerivAt f (-v r) r) :
    f s - f t = -(∫ r in t..s, v r) :=
  (ac_negative_gradient_integral f v hv M hb ht hs hac.symm hd).2

-- 08: zero speed gives equal endpoints; no division by M.
example {d : Nat} (f v : Real → Weight d) (hv : Measurable v) (s t : Real)
    (hb : ∀ᵐ r ∂volume.restrict (Ici (0 : Real)), norm (v r) ≤ 0)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hac : AbsolutelyContinuousOnInterval f s t)
    (hd : ∀ᵐ r ∂volume.restrict (Ici (0 : Real)), HasDerivAt f (-v r) r) :
    f s = f t := by
  have h := ac_negative_gradient_endpoint_bound f v hv 0 hb hs ht hac hd
  exact dist_eq_zero.mp (le_antisymm (by simpa using h) dist_nonneg)

-- 09: integrability is supplied before the integral equation.
example {d : Nat} (v : Real → Weight d) (hv : Measurable v) (M s t : Real)
    (hb : ∀ᵐ r ∂volume.restrict (Ici (0 : Real)), norm (v r) ≤ M)
    (hs : 0 ≤ s) (ht : 0 ≤ t) : IntervalIntegrable v volume s t :=
  intervalIntegrable_of_nonnegative_ae_bound v hv M hb hs ht

-- 10: AE replacement preserves both integrability and the signed integral.
example {d : Nat} {v u : Real → Weight d} {s t T : Real}
    (hs : s ∈ Icc (0 : Real) T) (ht : t ∈ Icc (0 : Real) T)
    (hv : IntervalIntegrable v volume s t)
    (he : v =ᵐ[volume.restrict (Icc (0 : Real) T)] u) :
    IntervalIntegrable u volume s t ∧ (∫ r in s..t, v r) = ∫ r in s..t, u r :=
  intervalIntegral_replace_ae_on_prefix hs ht hv he

variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}
variable (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
  [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)

-- 11: the law is the original pushforward, not a substitute distribution.
example (i : Fin 2) (t : Real) :
    X.measure i t = (initial i).map (X.characteristic i t) := rfl

-- 12: probability is derived.
example (i : Fin 2) (t : Real) : IsProbabilityMeasure (X.measure i t) :=
  X.measure_probability i t

-- 13: the initial map need only agree on the original closed support.
example (i : Fin 2) : X.measure i 0 = initial i := X.initial_law i

-- 14: the speed bound is AE in original labels and Lebesgue time.
example (i : Fin 2) :
    ∀ᵐ w ∂initial i, ∀ᵐ t ∂volume.restrict (Ici (0 : Real)),
      norm (X.pullbackGradient i t w) ≤ primalObjectiveSpeedBound d O a lambda p :=
  X.speed_bound_ae hl hp i

-- 15: actual AC ODE to integral equation, with integrability.
example (i : Fin 2) (s t : Real) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ∀ᵐ w ∂initial i,
      IntervalIntegrable (fun r => X.pullbackGradient i r w) volume s t ∧
      (X.characteristic i t w).val - (X.characteristic i s w).val =
        -(∫ r in s..t, X.pullbackGradient i r w) :=
  X.integral_equation_ae hl hp i s t hs ht

-- 16: an endpoint-AE set may depend on the fixed time pair.
example (i : Fin 2) (s t : Real) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ∀ᵐ w ∂initial i, dist (X.characteristic i s w) (X.characteristic i t w) ≤
      primalObjectiveSpeedBound d O a lambda p * dist s t :=
  X.endpoint_bound_ae hl hp i s t hs ht

-- 17: AFTER lifting each pair, all supported labels and all times.
example (i : Fin 2) (w : UnitSphere d) (hw : w ∈ (initial i).support) :
    LipschitzOnWith (Real.nnabs (primalObjectiveSpeedBound d O a lambda p))
      (fun t => X.characteristic i t w) (Ici (0 : Real)) :=
  X.supported_lipschitz hl hp i w hw

-- 18: joint continuity is a conclusion, not a data field.
example (i : Fin 2) :
    ContinuousOn (fun tw : Real × UnitSphere d => X.characteristic i tw.1 tw.2)
      ((Ici (0 : Real)) ×ˢ (initial i).support) :=
  X.supported_joint_continuity hl hp i

-- 19: supported time continuity includes time zero.
example (i : Fin 2) (w : UnitSphere d) (hw : w ∈ (initial i).support) :
    ContinuousOn (fun t => X.characteristic i t w) (Ici (0 : Real)) :=
  X.supported_time_continuity hl hp i w hw

variable (r : Real) (hc : ∀ i, TwoCapClass pole r (initial i))

-- 20: positivity of the first interval, also if lambda or speed vanishes.
example : 0 < primalInitialCapTime d O a pole r lambda p initial :=
  primalInitialCapTime_pos O a pole r lambda p initial hl hc

-- 21: actual angular displacement, not a chordal transport replacement.
example (i : Fin 2) (w : UnitSphere d) (hw : w ∈ (initial i).support)
    (t : Real) (ht : 0 ≤ t) :
    sphericalDistance (X.characteristic i t w) w ≤
      (Real.pi / 2) * primalObjectiveSpeedBound d O a lambda p * t :=
  X.angular_displacement_le hl hp i w hw t ht

-- 22: complete cap laws include both exact half masses.
example :
    0 < primalInitialCapTime d O a pole r lambda p initial ∧
    ∀ i t, t ∈ Icc (0 : Real) (primalInitialCapTime d O a pole r lambda p initial) →
      TwoCapClass pole r (X.measure i t) :=
  X.first_cap_laws hl hp r hc

-- 23: local identification remains AE under the CURRENT law.
example :
    ∀ᵐ t ∂volume.restrict
      (Icc (0 : Real) (primalInitialCapTime d O a pole r lambda p initial)), ∀ i,
    X.gradient i t =ᵐ[X.measure i t]
      sphericalObjectiveGradient O a pole lambda p (X.measure 0 t) (X.measure 1 t)
        teacher teacher i :=
  X.first_cap_gradient_ae hl hp r hc

-- 24: use the assembled endpoint, not a hand-supplied speed or cap premise.
example : 0 < primalInitialCapTime d O a pole r lambda p initial :=
  (primal_ac_characteristic_first_cap X hl hp r hc).2.1

end PaperFormalization.MatrixFactorization
