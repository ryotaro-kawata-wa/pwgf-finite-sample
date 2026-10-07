import PaperFormalization.MatrixFactorization.SphericalLogarithm

/-! MF02/03a boundary diagnostics. The driver separately generates
#check and #print axioms for EVERY explicitly named declaration in the new units.
These examples do not assert completion of the four local MF geometry results. -/
open MeasureTheory Set Filter
open scoped Topology
open PaperFormalization.MatrixFactorization
variable {d : Nat}

-- 01: zero-dimensional sphere has no artificial unit point.
example : IsEmpty (UnitSphere 0) := by
  refine ⟨fun w => ?_⟩
  have hz : w.val = 0 := Subsingleton.elim _ _
  exact unitSphere_ne_zero w hz

-- 02-06: angular endpoints, symmetry, range, and separation.
example (a : UnitSphere d) : sphericalDistance a a = 0 := sphericalDistance_self a
example (a : UnitSphere d) : sphericalDistance a (reflect a) = Real.pi := sphericalDistance_antipode a
example (a w : UnitSphere d) : sphericalDistance a w = sphericalDistance w a := sphericalDistance_comm a w
example (a w : UnitSphere d) : sphericalDistance a w ∈ Icc 0 Real.pi :=
  ⟨sphericalDistance_nonneg a w, sphericalDistance_le_pi a w⟩
example (a w : UnitSphere d) : sphericalDistance a w = 0 ↔ a = w := sphericalDistance_eq_zero_iff a w

-- 07-10: the strict cap condition and both distinct assignments.
example (a : UnitSphere d) (r : Real) (hr : r < Real.pi/2) :
    Disjoint (sphericalCap a r) (sphericalCap (reflect a) r) := sphericalCap_disjoint a r hr
example (a : UnitSphere d) (r : Real) (hr : 0 < r) : a ∈ sphericalCap a r := sphericalCap_pole_mem a r hr
example (a w : UnitSphere d) (r : Real) (hr : r < Real.pi/2) (hw : w ∈ sphericalCap a r) :
    assignedPole a w = a := assignedPole_positive a r hr hw
example (a w : UnitSphere d) (r : Real) (hr : r < Real.pi/2) (hw : w ∈ sphericalCap (reflect a) r) :
    assignedPole a w = reflect a := assignedPole_negative a r hr hw

-- 11-14: half-cost normalization and excluded cap radii.
example (a w : UnitSphere d) : 0 ≤ assignedCost a w := assignedCost_nonneg a w
example (a : UnitSphere d) : assignedCost a a = 0 := by
  simp [assignedCost, assignedPole_distance, Real.pi_pos.le]
example (a : UnitSphere d) (mu : Measure (UnitSphere d)) (h : TwoCapClass a 0 mu) : False :=
  (lt_irrefl 0) h.radius_pos
example (a : UnitSphere d) (mu : Measure (UnitSphere d)) (h : TwoCapClass a (Real.pi/2) mu) : False :=
  (lt_irrefl (Real.pi/2)) h.radius_lt

-- 15-18: exact marginals and genuinely nondeterministic competitor plans.
example (a : UnitSphere d) (r : Real) (mu : Measure (UnitSphere d)) (h : TwoCapClass a r mu) :
    mu.map (assignedPole a) = antipodalMeasure a := assignedPole_pushforward a r mu h
example (a : UnitSphere d) (r : Real) (mu : Measure (UnitSphere d)) (h : TwoCapClass a r mu) :
    (assignedPoleCoupling a r mu h).measure.map Prod.fst = mu ∧
    (assignedPoleCoupling a r mu h).measure.map Prod.snd = antipodalMeasure a :=
  ⟨(assignedPoleCoupling a r mu h).first_marginal, (assignedPoleCoupling a r mu h).second_marginal⟩
example (a : UnitSphere d) (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] :
    2 * ∫ w, assignedCost a w ∂mu ≤ sphericalTransportCost (productSphericalCoupling mu (antipodalMeasure a)) :=
  assignedPole_lower_bound a mu _
example (a : UnitSphere d) (r : Real) (mu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] (h : TwoCapClass a r mu) :
    sphericalTransportCost (assignedPoleCoupling a r mu h) ≤
      sphericalTransportCost (productSphericalCoupling mu (antipodalMeasure a)) :=
  assignedPoleCoupling_optimal a r mu h _

-- 19-22: exact infimum, diagonal zero boundary, product factor and radius bound.
example (a : UnitSphere d) (r : Real) (mu : Measure (UnitSphere d)) (h : TwoCapClass a r mu) :
    sphericalWassersteinSq mu (antipodalMeasure a) = 2 * ∫ w, assignedCost a w ∂mu :=
  sphericalWassersteinSq_antipodal a r mu h
example (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] : sphericalWassersteinSq mu mu = 0 :=
  sphericalWassersteinSq_self mu
example (a : UnitSphere d) : productAntipodalTransportSq a (antipodalMeasure a) (antipodalMeasure a) = 0 := by
  simp [productAntipodalTransportSq, sphericalWassersteinSq_self]
example (a : UnitSphere d) (r : Real) (mu : Measure (UnitSphere d)) (h : TwoCapClass a r mu) :
    sphericalWassersteinSq mu (antipodalMeasure a) ≤ r^2 := (sphericalWassersteinSq_cap_bound a r mu h).2

-- 23-24: no extra cap-preservation premise for actual small EXP perturbations.
example (a : UnitSphere d) (r : Real) (mu : Measure (UnitSphere d)) (h : TwoCapClass a r mu) :
    TwoCapClass a r (mu.map id) :=
  h.map id continuous_id (fun _ _ => ⟨fun hw => hw, fun hw => hw⟩)
example (a : UnitSphere d) (r : Real) (mu : Measure (UnitSphere d)) (h : TwoCapClass a r mu)
    (v : UnitSphere d → Weight d) (hv : Continuous v) (ht : ∀ w, inner Real w.val (v w) = 0) :
    ∀ᶠ t in 𝓝 (0 : Real), sphericalWassersteinSq (mu.map (sphericalExpFamily v ht t)) (antipodalMeasure a) =
      2 * ∫ w, assignedCost a (sphericalExpFamily v ht t w) ∂mu := by
  filter_upwards [fixed_assignment_sphericalExp a r mu h v ht hv] with t hh
  exact hh.2.2

-- 25-30: EXP is on the sphere; its derivatives are not straight output rays.
example (y : UnitSphere d) : sphericalExp y 0 (by simp) = y := sphericalExp_zero y _
example (y : UnitSphere d) (v : Weight d) (ht : inner Real y.val v = 0) :
    ‖(sphericalExp y v ht).val‖ = 1 := unitSphere_norm _
example (y : UnitSphere d) (v : Weight d) : sphereExpVelocity y v 0 = v := sphereExpVelocity_at_zero y v
example (y : UnitSphere d) (v : Weight d) :
    HasDerivAt (fun t : Real => sphereExpVector y (t • v)) v 0 := by
  simpa using sphereExpVector_hasDerivAt y v 0
example (y : UnitSphere d) (v : Weight d) :
    HasDerivAt (sphereExpVelocity y v) (-(‖v‖^2) • y.val) 0 := by
  simpa using sphereExpVelocity_hasDerivAt y v 0
example (y : UnitSphere d) (v : Weight d) (ht : inner Real y.val v = 0) (t : Real) :
    ‖sphereExpVelocity y v t‖ = ‖v‖ := sphereExpVelocity_norm y v ht t

-- 31-32: both genuine local inverses; the antipode is not silently admitted.
example (y w : UnitSphere d) (hs : sphericalDistance y w < Real.pi) :
    sphericalExp y (sphericalLog y w hs) (sphericalLog_tangent y w hs) = w := sphericalExp_log y w hs
example (y : UnitSphere d) (v : Weight d) (ht : inner Real y.val v = 0) (hs : ‖v‖ < Real.pi) :
    sphericalLog y (sphericalExp y v ht)
      (by rw [sphericalDistance_exp y v ht hs]; exact hs) = v := sphericalLog_exp y v ht hs

-- 33: the equator uses a fixed tie convention, outside the strict cap theorem.
example (a w : UnitSphere d) (hw : inner Real w.val a.val = 0) : assignedPole a w = a := by
  have hd : sphericalDistance w a = Real.pi/2 := by simp [sphericalDistance, hw]
  unfold assignedPole
  rw [sphericalDistance_reflect_right, hd]
  exact if_pos (by linarith)

-- 34: reflection equivariance is only used on the source cap union.
example (a w : UnitSphere d) (r : Real) (hr : r < Real.pi/2)
    (hw : w ∈ sphericalCap a r ∪ sphericalCap (reflect a) r) :
    assignedPole a (reflect w) = reflect (assignedPole a w) := assignedPole_reflect_on_caps a r hr hw

-- 35: zero tangent vector at any signed time.
example (y : UnitSphere d) (t : Real) :
    HasDerivAt (fun s : Real => sphereExpVector y (s • (0 : Weight d))) 0 t := by
  simpa [sphereExpVelocity] using sphereExpVector_hasDerivAt y 0 t

-- 36: the antipodal target retains the exact probability normalization.
example (a : UnitSphere d) : antipodalMeasure a Set.univ = 1 := measure_univ
