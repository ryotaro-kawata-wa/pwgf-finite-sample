import PaperFormalization.MatrixFactorization.SourceCharacteristicSupport

/-! # The printed two-margin basin on an existing cap interval

Both thresholds are the literal source fourth-norm constants. Compactness
supplies the common initial support bound; the derived particle barrier applies
to the full current closed supports. No extension of the given time interval
or global cap-free characteristic representation is asserted here.
-/
open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}

/-- The source's two closed margins at zstar pass to the actual initial cost.
The zero initial cost is included, and zstar need not be a coarse radius. -/
theorem source_basin_initial_margins
    (O : Finset Nat) (a : Nat → Weight h) (teacher : Measure (UnitSphere d))
    (lambda p radius zstar Z0 : Real) (hl : 0 < lambda) (hp3 : p < 3)
    (hZ0 : 0 ≤ Z0) (hinit : Z0 ≤ zstar)
    (hrad : sourceRadialConstant d O a teacher*zstar^((4-p)/2) ≤ lambda/2)
    (hforce : (sourceFittingConstant d O a teacher/lambda)*zstar^((3-p)/2) ≤ radius/2) :
    sourceRadialConstant d O a teacher*Z0^((4-p)/2) ≤ lambda/2 ∧
    (sourceFittingConstant d O a teacher/lambda)*Z0^((3-p)/2) ≤ radius/2 := by
  have hn := sourceBranchConstants_nonneg d O a teacher
  exact ⟨(mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hZ0 hinit (by linarith : 0 ≤ (4-p)/2)) hn.1).trans hrad,
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hZ0 hinit (by linarith : 0 ≤ (3-p)/2))
      (div_nonneg hn.2 hl.le)).trans hforce⟩

/-- The original closed supports have a uniform strictly interior barrier
under precisely the two printed margins and the original initial cost bound. -/
theorem SphericalCharacteristicSolution.support_strict_source_barrier
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0))
    (hl : 0 < lambda) (hp : 2 < p) (hp3 : p < 3)
    (zstar : Real) (hzstar : 0 < zstar)
    (hrad : sourceRadialConstant d O a teacher*zstar^((4-p)/2) ≤ lambda/2)
    (hforce : (sourceFittingConstant d O a teacher/lambda)*zstar^((3-p)/2) ≤ radius/2)
    (hinit : productAntipodalTransportSq pole (initial 0) (initial 1) ≤ zstar) :
    ∃ R0 : Real, 0 ≤ R0 ∧ R0 < radius ∧
      (∀ i w, w ∈ (initial i).support → sphericalPoleRadius pole w ≤ R0) ∧
      max R0 ((sourceFittingConstant d O a teacher/lambda)*
        (productAntipodalTransportSq pole (initial 0) (initial 1))^((3-p)/2)) < radius ∧
      (∀ i w, w ∈ (initial i).support → ∀ t ∈ Icc (0 : Real) T,
        sphericalPoleRadius pole (X.characteristic i t w) ≤
          max R0 ((sourceFittingConstant d O a teacher/lambda)*
            (productAntipodalTransportSq pole (initial 0) (initial 1))^((3-p)/2))) ∧
      (∀ i t, t ∈ Icc (0 : Real) T →
        (X.measure i t).support ⊆ {w | sphericalPoleRadius pole w ≤
          max R0 ((sourceFittingConstant d O a teacher/lambda)*
            (productAntipodalTransportSq pole (initial 0) (initial 1))^((3-p)/2))}) := by
  have hr := (X.cap 0 0 ⟨le_rfl,X.time_nonneg⟩).radius_pos
  have hz0 : 0 ≤ productAntipodalTransportSq pole (initial 0) (initial 1) := by
    rw [← X.transport_initial]
    exact X.productTransport_nonneg 0 ⟨le_rfl,X.time_nonneg⟩
  have hb := source_basin_initial_margins O a teacher lambda p radius zstar
    (productAntipodalTransportSq pole (initial 0) (initial 1)) hl hp3 hz0 hinit hrad hforce
  obtain ⟨R0,hR0,hR0r,hbound⟩ := X.initial_support_radius_lt
  refine ⟨R0,hR0,hR0r,hbound,max_lt hR0r (hb.2.trans_lt (by linarith)),?_,?_⟩
  · intro i w hw t ht
    exact X.particle_radius_le_source_barrier hO hunique hinitial hl hp hp3 hb.1
      R0 hR0 hbound i w hw t ht
  · intro i t ht
    exact X.support_radius_le_source_barrier hO hunique hinitial hl hp hp3 hb.1
      R0 hR0 hbound i t ht

/-- The printed basin gives uniformly smaller cap classes with exact half
masses, and the exact source decay and dissipation on this given interval. -/
theorem spherical_characteristic_source_cap_interval_support_control
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0))
    (hl : 0 < lambda) (hp : 2 < p) (hp3 : p < 3)
    (zstar : Real) (hzstar : 0 < zstar)
    (hrad : sourceRadialConstant d O a teacher*zstar^((4-p)/2) ≤ lambda/2)
    (hforce : (sourceFittingConstant d O a teacher/lambda)*zstar^((3-p)/2) ≤ radius/2)
    (hinit : productAntipodalTransportSq pole (initial 0) (initial 1) ≤ zstar) :
    ∃ R0 : Real, 0 ≤ R0 ∧ R0 < radius ∧
      let R := max R0 ((sourceFittingConstant d O a teacher/lambda)*
        (productAntipodalTransportSq pole (initial 0) (initial 1))^((3-p)/2))
      R < radius ∧
      (∀ t ∈ Icc (0 : Real) T,
        (∀ i : Fin 2, TwoCapClass pole ((R+radius)/2) (X.measure i t)) ∧
        (∀ i : Fin 2, (X.measure i t).support ⊆ {w | sphericalPoleRadius pole w ≤ R}) ∧
        X.transport t ≤
          (X.transport 0)/
            (1+(lambda*(p-2)/2)*(X.transport 0)^((p-2)/2)*t)^(2/(p-2)) ∧
        X.objective t ≤ X.objective 0) ∧
      (∀ t ∈ Ioo (0 : Real) T,
        HasDerivAt X.objective (-X.gradientEnergy t) t ∧
        deriv X.transport t ≤ -lambda*(X.transport t)^(p/2) ∧
        deriv X.objective t ≤ -(lambda^2/4)*(X.transport t)^(p-1)) := by
  obtain ⟨R0,hR0,hR0r,hbound,hRr,hparticle,hsupport⟩ :=
    X.support_strict_source_barrier hO hunique hinitial hl hp hp3 zstar hzstar hrad hforce hinit
  let R := max R0 ((sourceFittingConstant d O a teacher/lambda)*
    (productAntipodalTransportSq pole (initial 0) (initial 1))^((3-p)/2))
  have hR : 0 ≤ R := hR0.trans (le_max_left _ _)
  have hz0 : 0 ≤ productAntipodalTransportSq pole (initial 0) (initial 1) := by
    rw [← X.transport_initial]
    exact X.productTransport_nonneg 0 ⟨le_rfl,X.time_nonneg⟩
  have hsmall := (source_basin_initial_margins O a teacher lambda p radius zstar
    (productAntipodalTransportSq pole (initial 0) (initial 1)) hl hp3 hz0 hinit hrad hforce).1
  have hdec := spherical_characteristic_source_cap_interval_dissipation X hO hunique hinitial
    hl hp (by linarith : p < 4) hsmall
  refine ⟨R0,hR0,hR0r,hRr,?_,?_⟩
  · intro t ht
    refine ⟨?_,fun i => hsupport i t ht,(hdec.2.2.2.1 t ht).2.1,
      (hdec.2.2.2.1 t ht).2.2.2.2⟩
    intro i
    exact (X.cap i t ht).refine_radius_of_le R ((R+radius)/2)
      (by linarith) (by dsimp [R]; linarith) (by dsimp [R]; linarith)
      (hsupport i t ht)
  · intro t ht
    have hd := hdec.2.2.2.2.1 t ht
    exact ⟨hd.1,hd.2.1,hd.2.2.1⟩

end PaperFormalization.MatrixFactorization
