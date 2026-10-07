import PaperFormalization.MatrixFactorization.SphericalCharacteristicSupportClosure
import PaperFormalization.MatrixFactorization.SphericalCharacteristicSupportBarrier
import PaperFormalization.MatrixFactorization.SphericalSupportRadius
import PaperFormalization.MatrixFactorization.CoarseSupportMargin
import PaperFormalization.MatrixFactorization.TwoCapRadiusRefinement

/-! MF16 boundary diagnostics. These examples retain exact initial equalities,
zero transport, both poles and measurable pushforwards. They do not identify
the coarse coefficient with the manuscript's sharper fitting constant. -/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization.MF16Checks
open PaperFormalization.MatrixFactorization
set_option autoImplicit false

-- 1. The positive pole has zero assigned angular radius.
example {d : Nat} (pole : UnitSphere d) : sphericalPoleRadius pole pole = 0 := by
  simp [sphericalPoleRadius,assignedPole_distance,Real.pi_pos.le]

-- 2. The negative pole also has zero radius; the tie convention is irrelevant here.
example {d : Nat} (pole : UnitSphere d) : sphericalPoleRadius pole (reflect pole) = 0 := by
  have hp : sphericalDistance (reflect pole) pole = Real.pi := by
    rw [sphericalDistance_comm]
    simp
  simp [sphericalPoleRadius,assignedPole_distance,hp,Real.pi_pos.le]

-- 3. A differentiable curve passing through the pole has zero half-cost derivative,
-- even when its ambient velocity is nonzero.
example {d : Nat} (pole : UnitSphere d) (r : Real) (hr : 0 < r) (hrpi : r < Real.pi/2)
    (w : Real → UnitSphere d) (v : Weight d) (t : Real)
    (hw : HasDerivAt (fun s => (w s).val) v t) (hpole : w t = pole) :
    HasDerivAt (fun s => assignedCost pole (w s)) 0 t := by
  have hm : w t ∈ sphericalCap pole r ∪ sphericalCap (reflect pole) r := by
    rw [hpole]
    exact Or.inl (sphericalCap_pole_mem pole r hr)
  have ha := assignedPole_positive pole r hrpi (sphericalCap_pole_mem pole r hr)
  simpa only [hpole,assignedGradient,ha,poleGradient_self,inner_zero_left] using
    assignedCost_curve_hasDerivAt pole r w v t hrpi hm hw

-- 4. The square-root factorization includes zero with noninteger quarter powers.
example : Real.sqrt (0 : Real) = (0 : Real)^((1:Real)/4)*(0 : Real)^((1:Real)/4) := by
  convert sqrt_eq_radial_powers (p := (5:Real)/2) (Z := 0)
    (by norm_num) (by norm_num) le_rfl using 1; norm_num

-- 5. The actual scalar absorption accepts p=5/2 without integer-power substitution.
example {C lambda Z Z0 r : Real} (hC : 0 ≤ C) (hl : 0 < lambda)
    (hZ : 0 ≤ Z) (hZ0 : Z ≤ Z0) (hr : 0 ≤ r)
    (hb : C/lambda*Z0^((1:Real)/4) ≤ r) :
    C*Real.sqrt Z*r-lambda*Z^((1:Real)/4)*r^2 ≤ 0 := by
  have ha : ((5:Real)/2)/2-1 = (1:Real)/4 := by norm_num
  have he : (3-(5:Real)/2)/2 = (1:Real)/4 := by norm_num
  simpa only [ha,he] using radial_forcing_absorbed (p := (5:Real)/2)
    hC hl (by norm_num) (by norm_num) hZ hZ0 hr (by simpa only [he] using hb)

-- 6. Zero fitting coefficient still leaves a strictly positive sufficient basin.
example {lambda r : Real} (hl : 0 < lambda) (hr : 0 < r) :
    0 < coarseSupportBasin lambda ((5:Real)/2) 0 r :=
  coarseSupportBasin_pos lambda ((5:Real)/2) 0 r hl le_rfl hr

-- 7. The scalar support barrier permits exact equality at the initial barrier level.
example {f : Real → Real} {T R : Real} (hc : ContinuousOn f (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, DifferentiableAt Real f t) (hinit : f 0 = R)
    (hn : ∀ t ∈ Ioo 0 T, R < f t → deriv f t ≤ 0) :
    ∀ t ∈ Icc 0 T, f t ≤ R :=
  scalar_support_barrier hc hd hinit.le hn

-- 8. A zero-length interval needs no derivative at its sole time point.
example (f : Real → Real) : ∀ t ∈ Icc (0 : Real) 0, f t ≤ f 0 := by
  apply scalar_support_barrier
  · simpa only [Icc_self] using (continuousOn_singleton f (0 : Real))
  · simp
  · exact le_rfl
  · simp

-- 9. Zero initial transport removes the forcing part of the actual particle barrier.
example {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
    {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
    {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hu : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hi : initial 1 = reflectedMeasure (initial 0))
    (hl : 0 < lambda) (hp : 2 < p) (hp3 : p < 3)
    (hz : productAntipodalTransportSq pole (initial 0) (initial 1) = 0)
    (R0 : Real) (hR0 : 0 ≤ R0)
    (hb : ∀ i w, w ∈ (initial i).support → sphericalPoleRadius pole w ≤ R0)
    (i : Fin 2) (w : UnitSphere d) (hw : w ∈ (initial i).support)
    (t : Real) (ht : t ∈ Icc 0 T) :
    sphericalPoleRadius pole (X.characteristic i t w) ≤ R0 := by
  have hs : productAntipodalTransportSq pole (initial 0) (initial 1) ≤
      coarseRadialRadius lambda p (fittingCurvatureConstant d O a/64) := by
    rw [hz]
    exact (coarseRadialRadius_pos lambda p _ hl
      (div_nonneg (fittingCurvatureConstant_nonneg d O a) (by norm_num))).le
  simpa only [hz,Real.zero_rpow (by linarith : (3-p)/2 ≠ 0),mul_zero,max_eq_left hR0] using
    X.particle_radius_le_initial_barrier hO hu hi hl hp hp3 hs R0 hR0 hb i w hw t ht

-- 10. A closed support bound may be attained, and both refined caps retain exact half mass.
example {d : Nat} {pole : UnitSphere d} {radius : Real} {mu : Measure (UnitSphere d)}
    (hc : TwoCapClass pole radius mu) (R r' : Real) (hr : 0 < r')
    (hR : R < r') (hrr : r' < radius)
    (hb : mu.support ⊆ {w | sphericalPoleRadius pole w ≤ R}) :
    mu (sphericalCap pole r') = (1/2 : ENNReal) ∧
      mu (sphericalCap (reflect pole) r') = (1/2 : ENNReal) := by
  have hnew := hc.refine_radius_of_le R r' hr hR hrr hb
  exact ⟨hnew.positive_mass,hnew.negative_mass⟩

-- 11. The complete pushed support is controlled with only measurability of the map.
example {d : Nat} (pole : UnitSphere d) (mu : Measure (UnitSphere d))
    (f : UnitSphere d → UnitSphere d) (hf : Measurable f) (R : Real)
    (hb : ∀ w ∈ mu.support, sphericalPoleRadius pole (f w) ≤ R)
    (w : UnitSphere d) (hw : w ∈ (mu.map f).support) : sphericalPoleRadius pole w ≤ R :=
  sphericalPoleRadius_support_map_le pole mu f hf R hb hw

-- 12. Refinement still supplies the optimal all-coupling transport formula, not a new cost definition.
example {d : Nat} {pole : UnitSphere d} {radius : Real} {mu : Measure (UnitSphere d)}
    (hc : TwoCapClass pole radius mu) (r' : Real) (hr : 0 < r') (hrr : r' < radius)
    (hb : mu.support ⊆ {w | sphericalPoleRadius pole w < r'}) :
    sphericalWassersteinSq mu (antipodalMeasure pole) = 2*∫ w, assignedCost pole w ∂mu :=
  sphericalWassersteinSq_antipodal pole r' mu (hc.refine_radius r' hr hrr hb)

-- 13. Equality at the positive coarse basin still leaves half the cap radius.
example (lambda p C r : Real) (hl : 0 < lambda) (hp3 : p < 3)
    (hC : 0 ≤ C) (hr : 0 < r) :
    (C/lambda)*(coarseSupportBasin lambda p C r)^((3-p)/2) ≤ r/2 :=
  (coarseSupportBasin_bounds lambda p C r _ hl hp3 hC hr
    (coarseSupportBasin_pos lambda p C r hl hC hr).le le_rfl).2

-- 14. No additional mean-distance condition is needed after imposing the combined basin.
example (lambda p C r Z0 : Real)
    (hs : Z0 ≤ coarseSupportBasin lambda p C r) :
    Z0 ≤ coarseRadialRadius lambda p (C/64) := hs.trans (min_le_left _ _)

section ActualEndpoint
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}
variable (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
  [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
  (hu : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
  (hi : initial 1 = reflectedMeasure (initial 0))
  (hl : 0 < lambda) (hp : 2 < p) (hp3 : p < 3)

-- 15. The closed initial endpoint yields a strict, common current-support margin.
example (hs : productAntipodalTransportSq pole (initial 0) (initial 1) =
    coarseSupportBasin lambda p (fittingCurvatureConstant d O a) radius) :
    ∃ R : Real, R < radius ∧ ∀ i t, t ∈ Icc (0 : Real) T →
      (X.measure i t).support ⊆ {w | sphericalPoleRadius pole w ≤ R} := by
  obtain ⟨R0,hR0,hR0r,hb,hRr,hparticle,hsupport⟩ :=
    X.support_strict_barrier hO hu hi hl hp hp3 hs.le
  exact ⟨_,hRr,hsupport⟩

-- 16. The final actual endpoint yields one smaller cap radius for the whole interval.
example (hs : productAntipodalTransportSq pole (initial 0) (initial 1) ≤
    coarseSupportBasin lambda p (fittingCurvatureConstant d O a) radius) :
    ∃ r' : Real, 0 < r' ∧ r' < radius ∧
      ∀ i t, t ∈ Icc (0 : Real) T → TwoCapClass pole r' (X.measure i t) := by
  obtain ⟨R0,hR0,hR0r,hRr,hclosed,hopen⟩ :=
    spherical_characteristic_cap_interval_support_control X hO hu hi hl hp hp3 hs
  let R := max R0 ((fittingCurvatureConstant d O a/lambda)*
    (productAntipodalTransportSq pole (initial 0) (initial 1))^((3-p)/2))
  have hn : 0 ≤ R := hR0.trans (le_max_left _ _)
  have hr := (X.cap 0 0 ⟨le_rfl,X.time_nonneg⟩).radius_pos
  refine ⟨(R+radius)/2,by linarith,?_,?_⟩
  · dsimp [R]; linarith
  · intro i t ht
    exact (hclosed t ht).1 i
end ActualEndpoint

end PaperFormalization.MatrixFactorization.MF16Checks
