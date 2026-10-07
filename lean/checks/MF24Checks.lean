import PaperFormalization.MatrixFactorization.SupportedEndpointBounds

/-! MF24 boundary/type diagnostics. See `MF24_VALIDATION.md` for executed checks.
These examples keep primal derivative inputs and all AE qualifiers explicit.
They do not claim a global WGF theorem or full-support equality of arbitrary
measurable velocity representatives. All named declarations are separately
queried by the unit driver's generated type/axiom audit.
-/
open MeasureTheory Set Filter
open scoped Topology
open PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

-- 01: the zero test is tangent and bounded even in an empty sphere.
example (d : Nat) (w : UnitSphere d) : (BoundedTangentTest.zero d).field w = 0 := rfl

-- 02: negative tests retain the literal field and its bound.
example {d : Nat} (V : BoundedTangentTest d) (w : UnitSphere d) :
    V.neg.field w = -V.field w := rfl

-- 03: bounded Borel tests, not only continuous tests, have genuine L2 moments.
example {d : Nat} (V : BoundedTangentTest d) (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu] :
    Integrable (fun w => norm (V.field w)^2) mu := V.norm_sq_integrable mu

-- 04: the zero measure does not require a probability instance.
example {d : Nat} (V : BoundedTangentTest d) :
    Integrable V.field (0 : Measure (UnitSphere d)) := V.integrable 0

-- 05: the chosen tangent representative is pointwise tangent.
example {d : Nat} (g : UnitSphere d → Weight d) (w : UnitSphere d) :
    inner Real w.val (tangentVersion g w) = 0 := tangentVersion_tangent g w

-- 06: an original L2 tangent representative is unchanged only almost everywhere.
example {d : Nat} (mu : Measure (UnitSphere d)) (g : UnitSphere d → Weight d)
    (ht : ∀ᵐ w ∂mu, inner Real w.val (g w) = 0) :
    tangentVersion g =ᵐ[mu] g := tangentVersion_ae_eq mu g ht

-- 07: the cone estimate does not itself assume or imply derivative existence.
example {f : Real → Real} {D L : Real} (hd : HasDerivAt f D 0)
    (hu : ∀ᶠ t in 𝓝 (0 : Real), f t ≤ f 0+L*|t|) : |D| ≤ L :=
  derivative_abs_le_of_upper_cone hd hu

-- 08: the negative-time side is needed to bound a negative derivative.
example : |(-1 : Real)| ≤ 1 := by
  apply derivative_abs_le_of_upper_cone (f := fun t : Real => -t)
    (hasDerivAt_neg' (0 : Real))
  filter_upwards with t
  simpa using neg_le_abs t

-- 09: actual EXP is the identity at zero time.
example {d : Nat} (V : BoundedTangentTest d) (w : UnitSphere d) : V.expMap 0 w = w := V.expMap_zero w

-- 10: original pushforward law at zero, not an abstract law equality.
example {d : Nat} (V : BoundedTangentTest d) (mu : Measure (UnitSphere d)) :
    V.push mu 0 = mu := V.push_zero mu

-- 11: arbitrary signed times still produce a probability law.
example {d : Nat} (V : BoundedTangentTest d) (mu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] (t : Real) : IsProbabilityMeasure (V.push mu t) := V.push_probability mu t

-- 12: spatial measurability does not demand continuity of V.
example {d : Nat} (V : BoundedTangentTest d) (t : Real) : Measurable (V.expMap t) := V.expMap_measurable t

-- 13: time continuity is pointwise in the original label.
example {d : Nat} (V : BoundedTangentTest d) (w : UnitSphere d) :
    Continuous (fun t : Real => V.expMap t w) := V.expMap_time_continuous w

-- 14: the value bound concerns the true infimum over every coupling.
example {d : Nat} (V : BoundedTangentTest d) (mu nu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    ∀ᶠ t in 𝓝 (0 : Real), sphericalWassersteinSq (V.push mu t) nu ≤
      sphericalWassersteinSq mu nu+(2*Real.pi*(∫ w, norm (V.field w) ∂mu))*|t| :=
  V.transport_upper_near_zero mu nu

-- 15: no cap or optimal-dual representation is needed for the essential bound.
example {d : Nat} (mu nu : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu] (g : UnitSphere d → Weight d)
    (H : HasSphereFirstVariation mu (halfTransportFunctional nu) g) :
    ∀ᵐ w ∂mu, norm (g w) ≤ Real.pi := halfTransport_firstVariation_norm_le mu nu g H

-- 16: uniqueness remains an equality of representatives modulo the original law.
example {d : Nat} (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu]
    (J : Measure (UnitSphere d) → Real) (g k : UnitSphere d → Weight d)
    (H : HasSphereFirstVariation mu J g) (K : HasSphereFirstVariation mu J k) :
    g =ᵐ[mu] k := H.unique_ae K

-- 17: a measurable null-set modification cannot change a primal test derivative.
example {d : Nat} (mu : Measure (UnitSphere d))
    (J : Measure (UnitSphere d) → Real) (g k : UnitSphere d → Weight d)
    (H : HasSphereFirstVariation mu J g) (hk : Measurable k) (he : g =ᵐ[mu] k) :
    HasSphereFirstVariation mu J k := H.congr_gradient_ae hk he

-- 18: the local derivative is constructed from the original cap law.
example {d : Nat} (pole : UnitSphere d) (r : Real) (mu : Measure (UnitSphere d))
    (hc : TwoCapClass pole r mu) :
    HasSphereFirstVariation mu (halfTransportFunctional (antipodalMeasure pole)) (assignedGradient pole) :=
  cap_halfTransport_firstVariation pole r mu hc

-- 19: poles and atomic cap measures are not excluded from local AE identification.
example {d : Nat} (pole : UnitSphere d) (r : Real) (mu : Measure (UnitSphere d))
    (hc : TwoCapClass pole r mu) (g : UnitSphere d → Weight d)
    (H : HasSphereFirstVariation mu (halfTransportFunctional (antipodalMeasure pole)) g) :
    g =ᵐ[mu] assignedGradient pole := cap_primal_gradient_eq_assigned_ae pole r mu hc g H

-- 20: balanced assigned mass gives optimality without a cap or continuous map.
example {d : Nat} (pole : UnitSphere d) (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    (hm : mu.map (assignedPole pole) = antipodalMeasure pole) :
    sphericalWassersteinSq mu (antipodalMeasure pole) = 2*(∫ w, assignedCost pole w ∂mu) :=
  balanced_assignment_formula pole mu hm

-- 21: uniform short times retain labels for bounded Borel fields.
example {d : Nat} (V : BoundedTangentTest d) (pole : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (hc : TwoCapClass pole r mu) :
    ∀ᶠ t in 𝓝 (0 : Real), ∀ w ∈ mu.support,
      sphericalDistance (V.expMap t w) (assignedPole pole w) < r ∧
      assignedPole pole (V.expMap t w) = assignedPole pole w := V.assigned_near_zero pole r mu hc

-- 22: the regularizer bound vanishes at lambda=0 for any real p.
example (p : Real) : primalMetricSpeedBound 0 p = 0 := by simp [primalMetricSpeedBound]

-- 23: a noninteger source-range exponent is passed unchanged.
example {d : Nat} (pole : UnitSphere d) (lambda : Real) (hl : 0 ≤ lambda)
    (mu other : Measure (UnitSphere d)) [IsProbabilityMeasure mu] [IsProbabilityMeasure other]
    (g : UnitSphere d → Weight d)
    (H : HasSphereFirstVariation mu (partialMetricFunctional pole lambda (5/2) other) g) :
    ∀ᵐ w ∂mu, norm (g w) ≤ primalMetricSpeedBound lambda (5/2) :=
  primalMetricGradient_norm_le pole lambda (5/2) hl (by norm_num) mu other g H

-- 24: the zero regularizer has zero first variation; no positive Z is required.
example {d : Nat} (pole : UnitSphere d) (r : Real) (mu other : Measure (UnitSphere d))
    (hc : TwoCapClass pole r mu) [IsProbabilityMeasure other] :
    HasSphereFirstVariation mu (partialMetricFunctional pole 0 (5/2) other) (fun _ => 0) := by
  have hz : metricGradient pole 0 (5/2) mu other = (fun _ => 0) := by
    funext w
    simp only [metricGradient, zero_mul, zero_smul]
  simpa only [hz] using
    cap_partialMetric_firstVariation pole r 0 (5/2) (by norm_num) mu other hc

-- 25: the full cap first variation has no supplied gradient or derivative premise.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (pole : UnitSphere d)
    (r lambda : Real) (mu other teacher : Measure (UnitSphere d)) (hc : TwoCapClass pole r mu)
    [IsProbabilityMeasure other] [IsProbabilityMeasure teacher] :
    HasSphereFirstVariation mu (partialObjectiveFunctional O a pole lambda (5/2) other teacher teacher)
      (sphericalObjectiveGradient O a pole lambda (5/2) mu other teacher teacher 0) :=
  cap_partialObjective_firstVariation O a pole r lambda (5/2) (by norm_num) mu other teacher teacher hc

-- 26: residual gradient existence follows from the full identity, not a second assumption.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (pole : UnitSphere d)
    (lambda p : Real) (mu other teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure other] [IsProbabilityMeasure teacher]
    (g : UnitSphere d → Weight d)
    (H : HasSphereFirstVariation mu (partialObjectiveFunctional O a pole lambda p other teacher teacher) g) :
    HasSphereFirstVariation mu (partialMetricFunctional pole lambda p other)
      (fun w => g w-sphericalFittingGradient O a mu other teacher teacher 0 w) :=
  primalMetricGradient_from_full O a pole lambda p mu other teacher teacher g H

-- 27: the full source gradient has a cap-free essential speed bound.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (pole : UnitSphere d)
    (lambda p : Real) (hl : 0 ≤ lambda) (hp : 2 < p)
    (mu other teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure other] [IsProbabilityMeasure teacher]
    (g : UnitSphere d → Weight d)
    (H : HasSphereFirstVariation mu (partialObjectiveFunctional O a pole lambda p other teacher teacher) g) :
    ∀ᵐ w ∂mu, norm (g w) ≤ primalObjectiveSpeedBound d O a lambda p :=
  primalObjectiveGradient_norm_le O a pole lambda p hl hp mu other teacher teacher g H

-- 28: both product factors are controlled, not only an output-coordinate ray.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (pole : UnitSphere d)
    (lambda p : Real) (hl : 0 ≤ lambda) (hp : 2 < p)
    (mu : Fin 2 → Measure (UnitSphere d)) (hmu : ∀ i, IsProbabilityMeasure (mu i))
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] (g : Fin 2 → UnitSphere d → Weight d)
    (H : ∀ i, HasSphereFirstVariation (mu i) (sourcePartialObjective O a pole lambda p mu teacher i) (g i)) :
    ∀ i, ∀ᵐ w ∂mu i, norm (g i w) ≤ primalObjectiveSpeedBound d O a lambda p :=
  (source_primal_gradient_statewise O a pole lambda p hl hp mu hmu teacher g H).1

-- 29: the cap conclusion is measure-AE in both factors, not everywhere on support.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (pole : UnitSphere d)
    (r lambda p : Real) (hl : 0 ≤ lambda) (hp : 2 < p)
    (mu : Fin 2 → Measure (UnitSphere d)) (hc : ∀ i, TwoCapClass pole r (mu i))
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] (g : Fin 2 → UnitSphere d → Weight d)
    (H : ∀ i, HasSphereFirstVariation (mu i) (sourcePartialObjective O a pole lambda p mu teacher i) (g i)) :
    ∀ i, g i =ᵐ[mu i] sphericalObjectiveGradient O a pole lambda p (mu 0) (mu 1) teacher teacher i :=
  (source_primal_gradient_statewise O a pole lambda p hl hp mu (fun i => (hc i).probability) teacher g H).2.2 r hc

-- 30: the source L2 input supplies L1 before any first-variation pairing is used.
example {d : Nat} (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu]
    (J : Measure (UnitSphere d) → Real) (g : UnitSphere d → Weight d)
    (H : HasSphereFirstVariation mu J g) : Integrable g mu := H.integrable

-- 31: time/label exchange explicitly asks for measurability on the product.
example {A : Type*} [MeasurableSpace A] (eta : Measure A) [SFinite eta] {d : Nat}
    (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    (Phi : A → UnitSphere d → UnitSphere d) (hPhi : ∀ t, Measurable (Phi t))
    (g : A → UnitSphere d → Weight d) (C : Real)
    (hm : Measurable (fun tw : A × UnitSphere d => g tw.1 (Phi tw.1 tw.2)))
    (hb : ∀ᵐ t ∂eta, ∀ᵐ w ∂mu.map (Phi t), norm (g t w) ≤ C) :
    ∀ᵐ w ∂mu, ∀ᵐ t ∂eta, norm (g t (Phi t w)) ≤ C :=
  ae_label_ae_time_bound_of_statewise eta mu Phi hPhi g C hm hb

-- 32: support lifting requires relative continuity, not density of the law.
example {d : Nat} (mu : Measure (UnitSphere d)) (f : UnitSphere d → Real)
    (hc : ContinuousOn f mu.support) (C : Real) (hb : ∀ᵐ w ∂mu, f w ≤ C) :
    ∀ w ∈ mu.support, f w ≤ C := support_le_of_continuousOn_ae mu f hc C hb

-- 33: continuous endpoint representatives are identified on the full support.
example {d : Nat} (mu : Measure (UnitSphere d)) (f k : UnitSphere d → UnitSphere d)
    (hf : ContinuousOn f mu.support) (hk : ContinuousOn k mu.support) (he : f =ᵐ[mu] k) :
    ∀ w ∈ mu.support, f w = k w := support_eq_of_ae mu f k hf hk he

-- 34: zero temporal speed is included, for any time domain.
example {d : Nat} (mu : Measure (UnitSphere d)) (Phi : Real → UnitSphere d → UnitSphere d)
    (D : Set Real) (hc : ∀ t ∈ D, ContinuousOn (Phi t) mu.support)
    (hb : ∀ s ∈ D, ∀ t ∈ D, ∀ᵐ w ∂mu, dist (Phi s w) (Phi t w) ≤ (0 : Real)*dist s t) :
    ∀ w ∈ mu.support, LipschitzOnWith (Real.nnabs 0) (fun t => Phi t w) D :=
  supported_endpoints_lipschitz mu Phi D 0 le_rfl hc hb

-- 35: joint continuity is derived from endpoint estimates rather than stored in a flow record.
example {d : Nat} (mu : Measure (UnitSphere d)) (Phi : Real → UnitSphere d → UnitSphere d)
    (D : Set Real) (K : Real) (hK : 0 ≤ K) (hc : ∀ t ∈ D, ContinuousOn (Phi t) mu.support)
    (hb : ∀ s ∈ D, ∀ t ∈ D, ∀ᵐ w ∂mu, dist (Phi s w) (Phi t w) ≤ K*dist s t) :
    ContinuousOn (fun tw : Real × UnitSphere d => Phi tw.1 tw.2) (D ×ˢ mu.support) :=
  supported_joint_continuity_of_ae_endpoint_bound mu Phi D K hK hc hb

-- 36: the energy bound uses true square integrability and the original probability.
example {d : Nat} (mu nu : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu] (g : UnitSphere d → Weight d)
    (H : HasSphereFirstVariation mu (halfTransportFunctional nu) g) :
    (∫ w, norm (g w)^2 ∂mu) ≤ Real.pi^2 := halfTransport_firstVariation_energy_le mu nu g H
