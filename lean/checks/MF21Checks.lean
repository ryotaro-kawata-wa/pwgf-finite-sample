import PaperFormalization.MatrixFactorization.SourceCharacteristicSupportClosure
import PaperFormalization.MatrixFactorization.SourceCharacteristicIntegratedBounds
import PaperFormalization.MatrixFactorization.ExactSupportRadius
import PaperFormalization.MatrixFactorization.SourceBasinExistence
import PaperFormalization.MatrixFactorization.SourceExactSupportBarrier

/-! Boundary diagnostics for the exact source initial margin on a given cap interval. -/
open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- 1. Complementary-power absorption includes zero without dividing by it. -/
example (C : Real) : C*(0 : Real)^2 ≤ (0 : Real)*0^(3/2 : Real) := by
  apply source_power_error_absorbed (by norm_num) (by norm_num) (by norm_num)
  norm_num

/-- 2. A zero fitting coefficient admits an outer level at any nonnegative datum. -/
example (z lambda : Real) (hz : 0 ≤ z) (hl : 0 < lambda) :
    ∃ R : Real, z < R ∧ 0 < R ∧ (0 : Real)*R^(2-(3/2 : Real)) < lambda := by
  apply source_initial_margin_outer hz (by norm_num) hl
  simp only [zero_mul]
  positivity

/-- 3. Initial equality, rather than a strict half-margin, supplies the outer level. -/
example : ∃ R : Real, 1 < R ∧ 0 < R ∧ (1 : Real)*R^(2-(3/2 : Real)) < 2 := by
  apply source_initial_margin_outer (by norm_num) (by norm_num) (by norm_num)
  norm_num

/-- 4. The exact initial threshold is retained by the full differential inequality. -/
example (f : Real → Real) (T : Real) (hT : 0 ≤ T)
    (hc : ContinuousOn f (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, DifferentiableAt Real f t)
    (hn : ∀ t ∈ Icc 0 T, 0 ≤ f t) (h0 : f 0 = 1)
    (hi : ∀ t ∈ Ioo 0 T, deriv f t ≤ -2*2*(f t)^(3/2 : Real)+2*1*(f t)^2) :
    ∀ t ∈ Icc 0 T, f t ≤ 1 := by
  have hb := scalar_source_initial_margin hT (by norm_num : (0 : Real) < 2)
    (by norm_num : (0 : Real) ≤ 1) (by norm_num : (1 : Real) < 3/2)
    (by norm_num : (3/2 : Real) < 2) hc hd hn hi (by norm_num [h0])
  simpa only [h0] using hb.2.1

/-- 5. A zero datum stays zero under the original inequality, without a no-hitting premise. -/
example (f : Real → Real) (T lambda C : Real) (hT : 0 ≤ T) (hl : 0 < lambda) (hC : 0 ≤ C)
    (hc : ContinuousOn f (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, DifferentiableAt Real f t)
    (hn : ∀ t ∈ Icc 0 T, 0 ≤ f t) (h0 : f 0 = 0)
    (hi : ∀ t ∈ Ioo 0 T, deriv f t ≤ -2*lambda*(f t)^(3/2 : Real)+2*C*(f t)^2) :
    ∀ t ∈ Icc 0 T, f t = 0 := by
  have hm : C*(f 0)^(2-(3/2 : Real)) ≤ lambda/2 := by
    norm_num [h0]
    positivity
  have hb := scalar_source_initial_margin hT hl hC (by norm_num : (1 : Real) < 3/2)
    (by norm_num : (3/2 : Real) < 2) hc hd hn hi hm
  intro t ht
  exact scalar_zero_persists hn hb.1 ⟨le_rfl,hT⟩ ht ht.1 h0

/-- 6. At T=0 there is no interior derivative requirement. -/
example (f : Real → Real) (lambda C : Real) (hl : 0 < lambda) (hC : 0 ≤ C)
    (hn : 0 ≤ f 0) (hm : C*(f 0)^(2-(3/2 : Real)) ≤ lambda/2) :
    AntitoneOn f (Icc 0 0) := by
  have hc : ContinuousOn f (Icc (0 : Real) 0) := by
    simpa only [Icc_self] using continuousOn_singleton f 0
  exact (scalar_source_initial_margin (by norm_num : (0 : Real) ≤ 0) hl hC
    (by norm_num : (1 : Real) < 3/2) (by norm_num : (3/2 : Real) < 2) hc
    (by simp) (by
      intro t ht
      have he : t = 0 := by simpa using ht
      simpa only [he] using hn)
    (by simp) hm).1

section Actual
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}
variable [IsProbabilityMeasure teacher]

/-- 7. The raw actual transport inequality remains valid at p=3 without smallness. -/
example (X : SphericalCharacteristicSolution O a pole radius lambda 3 teacher initial T)
    (hO : ∀ n ∈ O, Odd n)
    (hu : SphericalCharacteristicLawUnique O a pole radius lambda 3 teacher initial T)
    (hi : initial 1 = reflectedMeasure (initial 0)) (t : Real) (ht : t ∈ Ioo 0 T) :
    deriv X.transport t ≤ -2*lambda*(X.transport t)^(3/2 : Real)+
      2*sourceRadialConstant d O a teacher*(X.transport t)^2 :=
  X.transport_deriv_le_source_remainder hO hu hi (by norm_num) t ht

/-- 8. Persistence includes p=3; no support-confinement conclusion is requested. -/
example (X : SphericalCharacteristicSolution O a pole radius lambda 3 teacher initial T)
    (hO : ∀ n ∈ O, Odd n)
    (hu : SphericalCharacteristicLawUnique O a pole radius lambda 3 teacher initial T)
    (hi : initial 1 = reflectedMeasure (initial 0)) (hl : 0 < lambda)
    (hm : sourceRadialConstant d O a teacher*
      (productAntipodalTransportSq pole (initial 0) (initial 1))^(1/2 : Real) ≤ lambda/2) :
    AntitoneOn X.transport (Icc 0 T) := by
  apply (X.transport_persists_source hO hu hi hl (by norm_num) (by norm_num) ?_).1
  norm_num only at *
  exact hm

/-- 9. Zero initial transport identifies both actual current laws at every closed time. -/
example (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (hO : ∀ n ∈ O, Odd n)
    (hu : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hi : initial 1 = reflectedMeasure (initial 0)) (hl : 0 < lambda)
    (hp : 2 < p) (hp4 : p < 4)
    (hz : productAntipodalTransportSq pole (initial 0) (initial 1) = 0)
    (t : Real) (ht : t ∈ Icc 0 T) : ∀ i : Fin 2, X.measure i t = antipodalMeasure pole := by
  have hm : sourceRadialConstant d O a teacher*
      (productAntipodalTransportSq pole (initial 0) (initial 1))^((4-p)/2) ≤ lambda/2 := by
    rw [hz,Real.zero_rpow (by linarith : (4-p)/2 ≠ 0),mul_zero]
    positivity
  apply X.zero_transport_laws t ht
  exact X.transport_zero_persists_source hO hu hi hl hp hp4 hm 0 t
    ⟨le_rfl,X.time_nonneg⟩ ht ht.1 (by simpa only [X.transport_initial] using hz)

/-- 10. The actual zero-length cap interval retains the exact initial decay value. -/
example (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial 0)
    (hO : ∀ n ∈ O, Odd n)
    (hu : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial 0)
    (hi : initial 1 = reflectedMeasure (initial 0)) (hl : 0 < lambda)
    (hp : 2 < p) (hp4 : p < 4)
    (hm : sourceRadialConstant d O a teacher*
      (productAntipodalTransportSq pole (initial 0) (initial 1))^((4-p)/2) ≤ lambda/2) :
    X.transport 0 ≤ powerDecayProfile lambda ((p-2)/2)
      (productAntipodalTransportSq pole (initial 0) (initial 1)) 0 :=
  ((X.transport_decay_source hO hu hi hl hp hp4 hm).2.2 0 ⟨le_rfl,le_rfl⟩).2.1

/-- 11. Equality in the actual initial threshold is admissible for dissipation. -/
example (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (hO : ∀ n ∈ O, Odd n)
    (hu : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hi : initial 1 = reflectedMeasure (initial 0)) (hl : 0 < lambda)
    (hp : 2 < p) (hp4 : p < 4)
    (hm : sourceRadialConstant d O a teacher*
      (productAntipodalTransportSq pole (initial 0) (initial 1))^((4-p)/2) = lambda/2)
    (t : Real) (ht : t ∈ Ioo 0 T) :
    deriv X.transport t ≤ -lambda*(X.transport t)^(p/2) :=
  X.transport_deriv_le_source_from_initial hO hu hi hl hp hp4 hm.le t ht

/-- 12. Positive actual transport gives strictly negative full-objective derivative. -/
example (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (hO : ∀ n ∈ O, Odd n)
    (hu : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hi : initial 1 = reflectedMeasure (initial 0)) (hl : 0 < lambda)
    (hp : 2 < p) (hp4 : p < 4)
    (hm : sourceRadialConstant d O a teacher*
      (productAntipodalTransportSq pole (initial 0) (initial 1))^((4-p)/2) ≤ lambda/2)
    (t : Real) (ht : t ∈ Ioo 0 T) (hz : 0 < X.transport t) : deriv X.objective t < 0 := by
  have he := spherical_characteristic_source_cap_interval_dissipation X hO hu hi hl hp hp4 hm
  exact (he.2.2.2.2.1 t ht).2.2.2 hz

/-- 13. All three integrated adapters include a closed subinterval of length zero. -/
example (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (hO : ∀ n ∈ O, Odd n)
    (hu : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hi : initial 1 = reflectedMeasure (initial 0)) (hl : 0 < lambda)
    (hp : 2 < p) (hp4 : p < 4)
    (hm : sourceRadialConstant d O a teacher*
      (productAntipodalTransportSq pole (initial 0) (initial 1))^((4-p)/2) ≤ lambda/2)
    (s : Real) (hs : s ∈ Icc 0 T) :
    IntervalIntegrable (fun u => -deriv X.transport u) volume s s ∧
      (lambda^2/4)*(∫ u in s..s, (X.transport u)^(p-1)) ≤ X.objective s-X.objective s ∧
      lambda*(∫ u in s..s, (X.transport u)^(p/2)) ≤ X.transport s-X.transport s :=
  ⟨X.transport_deriv_intervalIntegrable_source hO hu hi hl hp hp4 hm s s hs.1 le_rfl hs.2,
    X.integrated_gradientEnergy_lower_source hO hu hi hl hp hp4 hm s s hs.1 le_rfl hs.2,
    X.integrated_transport_decay_source hO hu hi hl hp hp4 hm s s hs.1 le_rfl hs.2⟩

/-- 14. The actual initial transport controls the accumulated transport power. -/
example (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (hO : ∀ n ∈ O, Odd n)
    (hu : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hi : initial 1 = reflectedMeasure (initial 0)) (hl : 0 < lambda)
    (hp : 2 < p) (hp4 : p < 4)
    (hm : sourceRadialConstant d O a teacher*
      (productAntipodalTransportSq pole (initial 0) (initial 1))^((4-p)/2) ≤ lambda/2)
    (t : Real) (ht : t ∈ Icc 0 T) :
    lambda*(∫ u in (0 : Real)..t, (X.transport u)^(p/2)) ≤
      productAntipodalTransportSq pole (initial 0) (initial 1)-X.transport t := by
  simpa only [X.transport_initial] using
    X.integrated_transport_decay_source hO hu hi hl hp hp4 hm 0 t le_rfl ht.1 ht.2

/-- 15. Equality with zstar propagates the two printed margins to the actual later laws. -/
example (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (hO : ∀ n ∈ O, Odd n)
    (hu : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hi : initial 1 = reflectedMeasure (initial 0)) (hl : 0 < lambda)
    (hp : 2 < p) (hp3 : p < 3) (zstar : Real)
    (hrad : sourceRadialConstant d O a teacher*zstar^((4-p)/2) ≤ lambda/2)
    (hforce : (sourceFittingConstant d O a teacher/lambda)*zstar^((3-p)/2) ≤ radius/2)
    (hinit : productAntipodalTransportSq pole (initial 0) (initial 1) = zstar) :
    ∀ t ∈ Icc (0 : Real) T,
      sourceRadialConstant d O a teacher*(X.transport t)^((4-p)/2) ≤ lambda/2 ∧
      X.transport t ≤ zstar := by
  have hz0 : 0 ≤ productAntipodalTransportSq pole (initial 0) (initial 1) := by
    rw [← X.transport_initial]
    exact X.productTransport_nonneg 0 ⟨le_rfl,X.time_nonneg⟩
  have hm := source_basin_initial_margins O a teacher lambda p radius zstar
    (productAntipodalTransportSq pole (initial 0) (initial 1)) hl hp3 hz0 hinit.le hrad hforce
  have hb := X.transport_persists_source hO hu hi hl hp (by linarith) hm.1
  intro t ht
  exact ⟨(hb.2 t ht).2.2,(hb.2 t ht).2.1.trans_eq hinit⟩

/-- 16. At zero initial cost both printed margins hold without a positive cost assumption. -/
example (zstar : Real) (hz : 0 ≤ zstar) (hl : 0 < lambda) (hp3 : p < 3)
    (hrad : sourceRadialConstant d O a teacher*zstar^((4-p)/2) ≤ lambda/2)
    (hforce : (sourceFittingConstant d O a teacher/lambda)*zstar^((3-p)/2) ≤ radius/2) :
    sourceRadialConstant d O a teacher*(0 : Real)^((4-p)/2) ≤ lambda/2 ∧
      (sourceFittingConstant d O a teacher/lambda)*(0 : Real)^((3-p)/2) ≤ radius/2 :=
  source_basin_initial_margins O a teacher lambda p radius zstar 0 hl hp3 le_rfl hz hrad hforce

/-- 17. At p=5/2 and zero cost, the actual particle barrier is precisely the original support bound. -/
example (X : SphericalCharacteristicSolution O a pole radius lambda (5/2) teacher initial T)
    (hO : ∀ n ∈ O, Odd n)
    (hu : SphericalCharacteristicLawUnique O a pole radius lambda (5/2) teacher initial T)
    (hi : initial 1 = reflectedMeasure (initial 0)) (hl : 0 < lambda)
    (hz : productAntipodalTransportSq pole (initial 0) (initial 1) = 0)
    (R0 : Real) (hR0 : 0 ≤ R0)
    (hb : ∀ i w, w ∈ (initial i).support → sphericalPoleRadius pole w ≤ R0)
    (i : Fin 2) (w : UnitSphere d) (hw : w ∈ (initial i).support)
    (t : Real) (ht : t ∈ Icc 0 T) : sphericalPoleRadius pole (X.characteristic i t w) ≤ R0 := by
  have hm : sourceRadialConstant d O a teacher*
      (productAntipodalTransportSq pole (initial 0) (initial 1))^((4-(5/2 : Real))/2) ≤ lambda/2 := by
    norm_num [hz]
    positivity
  have hh := X.particle_radius_le_source_barrier hO hu hi hl (by norm_num) (by norm_num)
    hm R0 hR0 hb i w hw t ht
  have hpow : (0 : Real)^((3-(5/2 : Real))/2) = 0 := Real.zero_rpow (by norm_num)
  rw [hz,hpow,mul_zero,max_eq_left hR0] at hh
  exact hh

/-- 18. The printed basin yields a common smaller cap with both exact half masses. -/
example (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (hO : ∀ n ∈ O, Odd n)
    (hu : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hi : initial 1 = reflectedMeasure (initial 0)) (hl : 0 < lambda)
    (hp : 2 < p) (hp3 : p < 3) (zstar : Real) (hzstar : 0 < zstar)
    (hrad : sourceRadialConstant d O a teacher*zstar^((4-p)/2) ≤ lambda/2)
    (hforce : (sourceFittingConstant d O a teacher/lambda)*zstar^((3-p)/2) ≤ radius/2)
    (hinit : productAntipodalTransportSq pole (initial 0) (initial 1) ≤ zstar) :
    ∃ r' : Real, 0 < r' ∧ r' < radius ∧ ∀ i t, t ∈ Icc (0 : Real) T →
      (X.measure i t) (sphericalCap pole r') = (1/2 : ENNReal) ∧
      (X.measure i t) (sphericalCap (reflect pole) r') = (1/2 : ENNReal) := by
  obtain ⟨R0,hR0,_hR0r,hRr,hclosed,_hinterior⟩ :=
    spherical_characteristic_source_cap_interval_support_control X hO hu hi hl hp hp3
      zstar hzstar hrad hforce hinit
  let R := max R0 ((sourceFittingConstant d O a teacher/lambda)*
    (productAntipodalTransportSq pole (initial 0) (initial 1))^((3-p)/2))
  have hR : 0 ≤ R := hR0.trans (le_max_left _ _)
  change R < radius at hRr
  refine ⟨(R+radius)/2,by linarith,by linarith,?_⟩
  intro i t ht
  have hc := (hclosed t ht).1 i
  exact ⟨hc.positive_mass,hc.negative_mass⟩

/-- 19. The exact product support supremum is attained by a real initial particle. -/
example (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T) :
    ∃ (i : Fin 2) (w : UnitSphere d), w ∈ (initial i).support ∧
      sphericalPoleRadius pole w = productSphericalSupportRadius pole initial ∧
      sphericalPoleRadius pole w < radius := by
  have hR := X.initial_exact_support_radius
  obtain ⟨i,w,hw,he⟩ := hR.2.2.2
  exact ⟨i,w,hw,he,he.trans_lt hR.2.1⟩

/-- 20. The Dirac pole has exact radius zero, and every least upper bound agrees. -/
example (R : Real)
    (hR : IsLUB (sphericalPoleRadius pole '' (Measure.dirac pole).support) R) :
    sphericalSupportRadius pole (Measure.dirac pole) = 0 ∧ R = 0 := by
  have hs : (Measure.dirac pole).support ⊆ {pole} :=
    Measure.support_subset_of_isClosed isClosed_singleton (by simp)
  obtain ⟨w,hw,he⟩ := sphericalSupportRadius_attained pole (Measure.dirac pole)
  have hw' : w = pole := Set.mem_singleton_iff.mp (hs hw)
  have hpole : sphericalPoleRadius pole pole = 0 := by
    simp [sphericalPoleRadius,assignedPole,Real.pi_pos.le]
  have hz : sphericalSupportRadius pole (Measure.dirac pole) = 0 := by
    rw [← he,hw',hpole]
  exact ⟨hz,(hR.unique (sphericalSupportRadius_isLUB pole (Measure.dirac pole))).trans hz⟩

/-- 21. Empty activation has zero source coefficients yet still has a positive printed basin. -/
example (hr : 0 < radius) (hl : 0 < lambda) :
    sourceRadialConstant d ∅ a teacher = 0 ∧ sourceFittingConstant d ∅ a teacher = 0 ∧
    ∃ zstar : Real, 0 < zstar ∧
      sourceRadialConstant d ∅ a teacher*zstar^((4-(5/2 : Real))/2) ≤ lambda/2 ∧
      (sourceFittingConstant d ∅ a teacher/lambda)*zstar^((3-(5/2 : Real))/2) ≤ radius/2 := by
  refine ⟨?_,?_,source_basin_exists ∅ a teacher radius lambda (5/2) hr hl (by norm_num) (by norm_num)⟩
  · simp [sourceRadialConstant,gaussianSecondJetL4,finiteHermiteActivationJet]
  · simp [sourceFittingConstant,gaussianFirstJetL4,finiteHermiteActivationJet]

/-- 22. The current literal supremum obeys the displayed Rbar, not an existential replacement. -/
example (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (hO : ∀ n ∈ O, Odd n)
    (hu : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hi : initial 1 = reflectedMeasure (initial 0)) (hl : 0 < lambda)
    (hp : 2 < p) (hp3 : p < 3) (zstar : Real) (hzstar : 0 < zstar)
    (hrad : sourceRadialConstant d O a teacher*zstar^((4-p)/2) ≤ lambda/2)
    (hforce : (sourceFittingConstant d O a teacher/lambda)*zstar^((3-p)/2) ≤ radius/2)
    (hinit : productAntipodalTransportSq pole (initial 0) (initial 1) ≤ zstar)
    (t : Real) (ht : t ∈ Icc (0 : Real) T) :
    productSphericalSupportRadius pole (fun i => X.measure i t) ≤
      max (productSphericalSupportRadius pole initial)
        ((sourceFittingConstant d O a teacher/lambda)*
          (productAntipodalTransportSq pole (initial 0) (initial 1))^((3-p)/2)) ∧
    max (productSphericalSupportRadius pole initial)
      ((sourceFittingConstant d O a teacher/lambda)*
        (productAntipodalTransportSq pole (initial 0) (initial 1))^((3-p)/2)) < radius := by
  have hb := X.support_exact_source_barrier hO hu hi hl hp hp3 zstar hzstar hrad hforce hinit
  exact ⟨(hb.2.2 t ht).2.1,hb.1⟩

end Actual
end PaperFormalization.MatrixFactorization
