import PaperFormalization.MatrixFactorization.SphericalRegularizerClosure

/-! MF03 boundary diagnostics.
These examples exercise zero and signed-time cases, the strict cap boundary,
normalization factors, and noninteger powers. Execution is recorded separately
by scripts/verify_mf03.py; the presence of this file is not a validation claim.
-/
open MeasureTheory Set Filter
open scoped Topology
open PaperFormalization.MatrixFactorization
set_option autoImplicit false

-- 01: A zero tangent vector stays fixed at a negative time.
example {d : Nat} (w : UnitSphere d) :
    geodesicPoint w 0 (by simp) (-3) = w := by simp

-- 02: Signed time translation returns to the original point.
example {d : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) :
    geodesicPoint (geodesicPoint w v hv (-2)) (sphereExpVelocity w v (-2))
      (geodesicVelocity_tangent w v hv (-2)) 2 = w := by
  simpa using geodesicPoint_return w v hv (-2)

-- 03: The moving velocity remains tangent for negative time as well.
example {d : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) :
    inner Real (geodesicPoint w v hv (-3)).val (sphereExpVelocity w v (-3)) = 0 :=
  geodesicVelocity_tangent w v hv (-3)

-- 04: The removable radial singularity has value one.
example : sphericalRadialWeight 0 = 1 := by simp

-- 05: Positivity must not be extended to the equatorial boundary.
example : sphericalRadialWeight (Real.pi/2) = 0 := by
  simp [sphericalRadialWeight]

-- 06: The continuous radial coefficient has the expected parity.
example (r : Real) : sphericalRadialWeight (-r) = sphericalRadialWeight r := by
  simp [sphericalRadialWeight]

-- 07: The two Hessian bounds coincide at radius zero.
example : sphericalRadialWeight 0 ≤ 1 ∧ 1 ≤ sphericalRadialWeight 0 := by simp

-- 08: The gradient vanishes exactly at its own pole.
example {d : Nat} (y : UnitSphere d) : poleGradient y y = 0 := by simp

-- 09: The Hessian retains the tangent identity at that pole.
example {d : Nat} (y : UnitSphere d) (v : Weight d) :
    poleHessian y y v = (norm v)^2 := by simp

-- 10: A pole has zero first variation in every tangent direction.
example {d : Nat} (y : UnitSphere d) (v : Weight d) :
    poleCostSlope y y v = 0 := by simp

-- 11: Zero velocity has zero Hessian value away from the pole too.
example {d : Nat} (y w : UnitSphere d) : poleHessian y w 0 = 0 := by simp

-- 12: The exact half-cost formula includes negative signed time.
example {d : Nat} (y : UnitSphere d) (v : Weight d)
    (hv : inner Real y.val v = 0) (ht : norm ((-1/2 : Real) • v) < Real.pi) :
    poleCost y (geodesicPoint y v hv (-1/2)) = (norm v)^2/8 := by
  rw [poleCost_along_pole y v hv ht]
  ring

-- 13: The actual EXP curve has zero first cost derivative at a pole.
example {d : Nat} (y : UnitSphere d) (v : Weight d)
    (hv : inner Real y.val v = 0) :
    HasDerivAt (fun t => poleCost y (geodesicPoint y v hv t)) 0 0 := by
  simpa using poleCost_hasDerivAt_zero y y v hv (by simpa using Real.pi_pos)

-- 14: Its ordinary iterated derivative is the full squared speed.
example {d : Nat} (y : UnitSphere d) (v : Weight d)
    (hv : inner Real y.val v = 0) :
    deriv (deriv (fun t => poleCost y (geodesicPoint y v hv t))) 0 = (norm v)^2 := by
  simpa using (poleCost_second_derivative y y v hv (by simpa using Real.pi_pos)).deriv

-- 15: A stationary curve also has zero ordinary second derivative.
example {d : Nat} (y w : UnitSphere d) (hs : sphericalDistance w y < Real.pi) :
    HasDerivAt (deriv (fun t => poleCost y (geodesicPoint w 0 (by simp) t))) 0 0 := by
  simpa using poleCost_second_derivative y w 0 (by simp) hs

-- 16: The gradient formula has no ambient normal component.
example {d : Nat} (y w : UnitSphere d) :
    inner Real w.val (poleGradient y w) = 0 := poleGradient_tangent y w

-- 17: Nonnegative Hessian follows from cap geometry without a curvature premise.
example {d : Nat} (y w : UnitSphere d) (v : Weight d)
    (hs : sphericalDistance w y < Real.pi/2) : 0 ≤ poleHessian y w v := by
  exact (mul_nonneg (sphericalRadialWeight_pos (sphericalDistance_nonneg w y) hs).le
    (sq_nonneg (norm v))).trans (poleHessian_bounds y w v le_rfl hs).1

-- 18: The sharp upper bound includes nonunit tangent vectors.
example {d : Nat} (y w : UnitSphere d) (v : Weight d)
    (hs : sphericalDistance w y < Real.pi/2) : poleHessian y w v ≤ (norm v)^2 :=
  (poleHessian_bounds y w v le_rfl hs).2

-- 19: The antipode does not satisfy the shortest-LOG domain condition.
example {d : Nat} (y : UnitSphere d) :
    ¬ sphericalDistance y (reflect y) < Real.pi := by simp

-- 20: Simultaneous reflection preserves the original half-cost.
example {d : Nat} (y w : UnitSphere d) :
    poleCost (reflect y) (reflect w) = poleCost y w := by
  simp only [poleCost, sphericalDistance_reflect_reflect]

-- 21: Pointwise zero velocity implies zero product tangent energy.
example {d : Nat} (P : SphericalVariation d) (hv : ∀ i w, P.velocity i w = 0) :
    variationEnergy P = 0 := by simp [variationEnergy, hv]

-- 22: Zero L2 energy forces zero integrated Hessian in both factors.
example {d : Nat} (P : SphericalVariation d) (hE : variationEnergy P = 0) :
    variationSecond P = 0 := by
  have hb := variationSecond_bounds P
  rw [hE, mul_zero] at hb
  exact le_antisymm hb.2 hb.1

-- 23: Zero regularization strength gives the zero functional for every exponent.
example {d : Nat} (P : SphericalVariation d) (p t : Real) :
    variationRegularizer P 0 p t = 0 := by simp [variationRegularizer]

-- 24: The critical real exponent 5/2 has both derivatives zero at the origin.
example : HasDerivAt (fun t : Real => |t|^(5/2 : Real)) 0 0 ∧
    HasDerivAt (deriv (fun t : Real => |t|^(5/2 : Real))) 0 0 := by
  simpa using absPower_second_zero 1 (5/2) (by norm_num)

-- 25: Flatness does not rely on positivity of the scalar prefactor.
example : HasDerivAt (deriv (fun t : Real => (-3)*|t|^(5/2 : Real))) 0 0 :=
  (absPower_second_zero (-3) (5/2) (by norm_num)).2

-- 26: The power normalization is valid on the negative half-line.
example : (((-2 : Real)^2)^(5/4 : Real)) = |(-2 : Real)|^(5/2 : Real) := by
  convert square_rpow_half (-2) (5/2) using 1 <;> norm_num

-- 27: Zero product transport determines each original probability law.
example {d : Nat} (P : SphericalVariation d) (hz : variationTransport P 0 = 0) :
    P.measure 0 = antipodalMeasure P.pole ∧ P.measure 1 = antipodalMeasure P.pole :=
  ⟨zeroVariation_original_laws P hz 0, zeroVariation_original_laws P hz 1⟩

-- 28: At zero energy and zero target distance, transport is locally identically zero.
example {d : Nat} (P : SphericalVariation d) (hz : variationTransport P 0 = 0)
    (hE : variationEnergy P = 0) :
    ∀ᶠ t in 𝓝 (0 : Real), variationTransport P t = 0 := by
  simpa only [hE, mul_zero] using variationTransport_zero_quadratic P hz

-- 29: The same degenerate direction has locally zero regularizer for p=5/2.
example {d : Nat} (P : SphericalVariation d) (hz : variationTransport P 0 = 0)
    (hE : variationEnergy P = 0) (lambda : Real) :
    variationRegularizer P lambda (5/2) =ᶠ[𝓝 (0 : Real)] (fun _ => 0) := by
  simpa [hE] using variationRegularizer_zero_formula P lambda (5/2) hz

-- 30: The model's literal second derivative vanishes for that noninteger exponent.
example {d : Nat} (P : SphericalVariation d) (hz : variationTransport P 0 = 0)
    (lambda : Real) : deriv (deriv (variationRegularizer P lambda (5/2))) 0 = 0 :=
  (metricRegularizer_zero_variations P lambda (5/2) (by norm_num) hz).2.deriv

-- 31: The source-facing gradient also vanishes at zero target transport.
example {d : Nat} (P : SphericalVariation d) (hz : variationTransport P 0 = 0)
    (lambda : Real) (w : UnitSphere d) : regularizerGradient P lambda (5/2) w = 0 := by
  norm_num [regularizerGradient, hz]

-- 32: Positive curvature away from the target applies to 2<p<3 without integer powers.
example {d : Nat} (P : SphericalVariation d) (hz : 0 < variationTransport P 0)
    (hE : 0 < variationEnergy P) :
    0 < deriv (deriv (variationRegularizer P 1 (5/2))) 0 :=
  metricRegularizer_second_strictly_positive P 1 (5/2) (by norm_num) (by norm_num) hz hE

-- 33: Both contraction endpoints remain the actual original points.
example {d : Nat} (y w : UnitSphere d) (hs : sphericalDistance y w < Real.pi) :
    poleContraction y w hs 0 = y ∧ poleContraction y w hs 1 = w := by simp

-- 34: Halving angular distance quarters the half-squared cost.
example {d : Nat} (y w : UnitSphere d) (hs : sphericalDistance y w < Real.pi) :
    poleCost y (poleContraction y w hs (1/2)) = poleCost y w / 4 := by
  rw [poleCost, poleContraction_distance y w hs (by norm_num) (by norm_num),
    poleCost, sphericalDistance_comm w y]
  ring

-- 35: Reflection commutes with the midpoint contraction.
example {d : Nat} (y w : UnitSphere d) (hs : sphericalDistance y w < Real.pi) :
    poleContraction (reflect y) (reflect w) (by simpa only [sphericalDistance_reflect_reflect] using hs) (1/2) =
      reflect (poleContraction y w hs (1/2)) := poleContraction_reflected y w hs (1/2)

-- 36: For p=4, the rank-one coefficient is lambda*(p-2), with no missing factor two.
example {d : Nat} (P : SphericalVariation d) (hz : 0 < variationTransport P 0) :
    deriv (deriv (variationRegularizer P 2 4)) 0 =
      2*variationTransport P 0*variationSecond P + 4*(variationFirst P)^2 := by
  have h := (metricRegularizer_positive_variations P 2 4 (by norm_num) (by norm_num) hz).2.deriv
  norm_num at h
  simpa only [variationTransport_zero] using h
