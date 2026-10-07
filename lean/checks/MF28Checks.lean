import PaperFormalization.MatrixFactorization.IntegralL2PrimalBridge
import PaperFormalization.MatrixFactorization.PrimalACIntegralForm

/-! MF28 boundary diagnostics: actual L2 EXP laws, singular measures, signed
endpoints, and simultaneous label/time quantifiers. The separate driver
audits every named declaration, including the same-trajectory constructor.
-/
open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

-- 01: time zero needs no finiteness or density assumption.
example (mu : Measure (UnitSphere d)) (v : sphereTangentL2 mu) :
    sphereL2ExpPush mu v 0 = mu := by simp

-- 02: the zero direction leaves the actual law fixed for negative time too.
example (mu : Measure (UnitSphere d)) (t : Real) :
    sphereL2ExpPush mu 0 (-t) = mu := by simp

-- 03: scalar reversal is a law identity, not a pointwise quotient identity.
example (mu : Measure (UnitSphere d)) (v : sphereTangentL2 mu) (t : Real) :
    sphereL2ExpPush mu (-v) t = sphereL2ExpPush mu v (-t) := by
  simpa using sphereL2ExpPush_smul mu v (-1) t

-- 04: atomic laws are included in the probability result.
example (w : UnitSphere d) (v : sphereTangentL2 (Measure.dirac w)) (t : Real) :
    IsProbabilityMeasure (sphereL2ExpPush (Measure.dirac w) v t) :=
  sphereL2ExpPush_probability _ v t

-- 05: representative tangency holds at every point, including null points.
example (mu : Measure (UnitSphere d)) (v : sphereTangentL2 mu) (w : UnitSphere d) :
    inner Real w.val (sphereL2Representative v w) = 0 :=
  sphereL2Representative_tangent v w

-- 06: the field agrees with the quotient representative only almost everywhere.
example (mu : Measure (UnitSphere d)) (v : sphereTangentL2 mu) :
    sphereL2Representative v =ᵐ[mu] (v : Lp (Weight d) 2 mu) :=
  sphereL2Representative_ae_eq v

-- 07: genuine square integrability does not require a finite law.
example (mu : Measure (UnitSphere d)) (v : sphereTangentL2 mu) :
    Integrable (fun w => norm (sphereL2Representative v w)^2) mu :=
  sphereL2Representative_norm_sq_integrable v

-- 08: the inner-product integrand is genuinely integrable.
example (mu : Measure (UnitSphere d)) (u v : sphereTangentL2 mu) :
    Integrable (fun w => inner Real (sphereL2Representative u w)
      (sphereL2Representative v w)) mu := sphereL2Representative_pairing_integrable u v

-- 09: norm energy is the integral against the original law.
example (mu : Measure (UnitSphere d)) (v : sphereTangentL2 mu) :
    (∫ w, norm (sphereL2Representative v w)^2 ∂mu) = norm v^2 :=
  sphereL2Representative_energy v

-- 10: discontinuous bounded Borel tests use the same actual EXP pushforward.
example (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu]
    (V : BoundedTangentTest d) (t : Real) :
    sphereL2ExpPush mu (t • V.toSphereL2 mu) 1 = V.push mu t := V.toSphereL2_chart mu t

-- 11: an alternative tangent representative gives exactly the same law.
example (mu : Measure (UnitSphere d)) (v : sphereTangentL2 mu)
    (f : UnitSphere d → Weight d) (ht : ∀ w, inner Real w.val (f w) = 0)
    (he : sphereL2Representative v =ᵐ[mu] f) (t : Real) :
    sphereL2ExpPush mu v t = mu.map (sphericalExpFamily f ht t) :=
  sphereL2ExpPush_eq_of_representative mu v f ht he t

-- 12: the original supplied velocity representative is retained up to AE equality.
example (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu]
    (J : Measure (UnitSphere d) → Real) (v : sphereTangentL2 mu)
    (H : HasSphereL2FirstVariation mu J v) (g : UnitSphere d → Weight d)
    (hg : Measurable g) (he : sphereL2Representative v =ᵐ[mu] g) :
    HasSphereFirstVariation mu J g := H.to_primal_of_ae g hg he

-- 13: uniqueness concerns L2 classes, including atomic laws.
example (w : UnitSphere d) (J : Measure (UnitSphere d) → Real)
    (u v : sphereTangentL2 (Measure.dirac w))
    (H : HasSphereL2FirstVariation (Measure.dirac w) J u)
    (K : HasSphereL2FirstVariation (Measure.dirac w) J v) : u = v := H.unique K

-- 14: a stronger Frechet premise is sufficient, rather than mandatory.
example (mu : Measure (UnitSphere d)) (J : Measure (UnitSphere d) → Real)
    (g : sphereTangentL2 mu)
    (H : HasFDerivAt (fun v : sphereTangentL2 mu => J (sphereL2ExpPush mu v 1))
      (innerSL Real g) 0) : HasSphereL2FirstVariation mu J g :=
  sphereL2FirstVariation_of_hasFDerivAt mu J g H

-- 15: the Banach primitive includes reversed endpoints.
example (v : Real → Weight d) (s t : Real) (hv : IntervalIntegrable v volume t s) :
    AbsolutelyContinuousOnInterval (fun x => ∫ r in t..x, v r) t s :=
  integral_curve_absolutelyContinuous hv (by simp)

-- 16: a zero-length prefix does not impose a positive-time premise.
example (f v : Real → Weight d)
    (he : ∀ t ∈ Icc (0 : Real) 0, f t = f 0 - ∫ r in 0..t, v r) :
    AbsolutelyContinuousOnInterval f 0 0 :=
  integral_characteristic_ac le_rfl (by simp) he

-- 17: derivative recovery at a degenerate prefix remains an AE statement.
example (f v : Real → Weight d)
    (he : ∀ t ∈ Icc (0 : Real) 0, f t = f 0 - ∫ r in 0..t, v r) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : Real) 0), HasDerivAt f (-v t) t :=
  integral_characteristic_ae_ode le_rfl (by simp) he

-- 18: vector FTC does not assume a coordinatewise loss factor.
example (f v : Real → Weight d) (s t : Real)
    (hf : AbsolutelyContinuousOnInterval f t s) (hv : IntervalIntegrable v volume t s)
    (hd : ∀ᵐ r : Real, r ∈ uIcc t s → HasDerivAt f (v r) r) :
    (∫ r in t..s, v r) = f s - f t := integral_eq_sub_of_ac_ae_velocity hf hv hd

-- 19: integer prefixes suffice for the whole nonnegative time axis.
example {P : Real → Prop}
    (hP : ∀ n : Nat, ∀ᵐ t ∂volume.restrict (Icc (0 : Real) n), P t) :
    ∀ᵐ t ∂volume.restrict (Ici (0 : Real)), P t := ae_nonnegative_of_ae_nat_prefix hP

-- 20: arbitrary real endpoints, including reverse order, are preserved.
example (f v : Real → Weight d)
    (H : ∀ n : Nat, IntervalIntegrable v volume 0 n ∧
      ∀ t ∈ Icc (0 : Real) n, f t = f 0 - ∫ r in 0..t, v r)
    (s t : Real) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    AbsolutelyContinuousOnInterval f t s := integral_characteristic_ac_all_segments H t s ht hs

-- 21: ODE recovery requires actual prefix integrability.
example (f v : Real → Weight d)
    (H : ∀ n : Nat, IntervalIntegrable v volume 0 n ∧
      ∀ t ∈ Icc (0 : Real) n, f t = f 0 - ∫ r in 0..t, v r) :
    ∀ᵐ t ∂volume.restrict (Ici (0 : Real)), HasDerivAt f (-v t) t :=
  integral_characteristic_ae_ode_nonnegative H

-- 22: one conull label set supports all nonnegative time pairs.
example (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p) (i : Fin 2) :
    ∀ᵐ w ∂initial i, ∀ s t : Real, 0 ≤ s → 0 ≤ t →
      IntervalIntegrable (fun r => X.pullbackGradient i r w) volume s t ∧
      (X.characteristic i t w).val - (X.characteristic i s w).val =
        -(∫ r in s..t, X.pullbackGradient i r w) :=
  X.integral_equation_ae_all_times hl hp i

-- 23: lambda zero remains allowed in the original-label integral form.
example (X : PrimalACCharacteristicData O a pole 0 p teacher initial)
    [IsProbabilityMeasure teacher] (hp : 2 < p) (i : Fin 2) :
    ∀ᵐ w ∂initial i, ∀ t : Real, 0 ≤ t →
      IntervalIntegrable (fun r => X.pullbackGradient i r w) volume 0 t ∧
      (X.characteristic i t w).val = w.val - ∫ r in 0..t, X.pullbackGradient i r w :=
  X.integral_from_initial_label_ae le_rfl hp i

-- 24: an individual integer prefix includes its endpoints.
example (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p) (i : Fin 2) (n : Nat) :
    ∀ᵐ w ∂initial i,
      IntervalIntegrable (fun t => X.pullbackGradient i t w) volume 0 n ∧
      ∀ t ∈ Icc (0 : Real) n,
        (X.characteristic i t w).val = (X.characteristic i 0 w).val -
          ∫ r in 0..t, X.pullbackGradient i r w := X.integral_prefix_ae hl hp i n

end PaperFormalization.MatrixFactorization
