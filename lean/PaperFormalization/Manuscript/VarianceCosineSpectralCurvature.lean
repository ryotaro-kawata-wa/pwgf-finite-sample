import PaperFormalization.Manuscript.VarianceCosinePopulation
import PaperFormalization.Manuscript.VarianceCosineEscapeGeometry
import PaperFormalization.Manuscript.SourceCurvaturePath

/-! # The actual full sampled Hessian and its Rayleigh infimum
M13v VERIFIED UNIT (full example application remains open). Both the diagonal spatial block and the 1/N kernel block
are retained. The lower spectral edge is proved from quadratic forms and
explicit nonzero vectors; it is not defined to be the desired minimum.
N=1 is stated separately. N=0 is not used as a spectral application.
The source application uses N>=2.
-/
open Set MeasureTheory
open scoped BigOperators
namespace PaperFormalization.Manuscript
open Continuous

noncomputable def varianceCosineHessian (N : Nat) (a c : Real) :
    SourceFiniteConfiguration N 1 →L[Real] SourceFiniteConfiguration N 1 :=
  sampledBlockOperator
    (fun _ : Fin N => a • ContinuousLinearMap.id Real VarianceCosinePoint)
    (fun _ _ : Fin N => c • ContinuousLinearMap.id Real VarianceCosinePoint)

theorem varianceCosine_source_sampled_hessian (N : Nat) (a beta : Real)
    (z : VarianceCosineHilbert) (Y : SourceFiniteConfiguration N 1) :
    sampledMomentHessian varianceCosineEncodedFeature (varianceCosineObjective a beta) z Y =
      varianceCosineHessian N a (varianceCosineKernel a beta (varianceCosineDecode 0 z)) := by
  unfold sampledMomentHessian
  simp only [varianceCosine_source_spatial,varianceCosine_source_integral_hessian]
  rfl

theorem varianceCosineHessian_scalar_apply {N : Nat} (a c : Real)
    (v : SourceFiniteConfiguration N 1) (i : Fin N) :
    varianceCosineScalar (varianceCosineHessian N a c v i) =
      a*varianceCosineScalar (v i)+c*varianceCosineEmpiricalMean v := by
  simp only [varianceCosineHessian,sampledBlockOperator_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,map_add,map_smul,map_sum,
    Fintype.card_fin,smul_eq_mul,varianceCosineEmpiricalMean]
  rw [<- Finset.mul_sum]
  ring

theorem varianceCosine_configuration_norm_sq {N : Nat}
    (v : SourceFiniteConfiguration N 1) :
    norm v^2 = ∑ i : Fin N, (varianceCosineScalar (v i))^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro i _
  rw [<- varianceCosineScalar_abs,sq_abs]

theorem varianceCosineHessian_quadratic {N : Nat} (a c : Real)
    (v : SourceFiniteConfiguration N 1) :
    inner Real v (varianceCosineHessian N a c v) =
      a*norm v^2+c*(N : Real)⁻¹*(∑ i : Fin N, varianceCosineScalar (v i))^2 := by
  have hi (i : Fin N) : inner Real (v i) (varianceCosineHessian N a c v i) =
      a*(varianceCosineScalar (v i))^2+
      (c*(N : Real)⁻¹*(∑ j : Fin N, varianceCosineScalar (v j)))*varianceCosineScalar (v i) := by
    rw [<- varianceCosinePoint_scalar (varianceCosineHessian N a c v i),
      varianceCosine_inner_point,varianceCosineHessian_scalar_apply]
    dsimp [varianceCosineEmpiricalMean]
    ring
  rw [PiLp.inner_apply]
  simp_rw [hi]
  rw [Finset.sum_add_distrib,<- Finset.mul_sum,<- Finset.mul_sum,
    <- varianceCosine_configuration_norm_sq]
  ring

theorem varianceCosine_mean_direction_energy {N : Nat} (hN : 0 < N)
    (v : SourceFiniteConfiguration N 1) :
    0 <= (N : Real)⁻¹*(∑ i : Fin N, varianceCosineScalar (v i))^2 ∧
      (N : Real)⁻¹*(∑ i : Fin N, varianceCosineScalar (v i))^2 <= norm v^2 := by
  have hn : (N : Real) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hCS : (∑ i : Fin N, varianceCosineScalar (v i))^2 <= (N : Real)*norm v^2 := by
    simpa only [Finset.card_univ,Fintype.card_fin,varianceCosine_configuration_norm_sq] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => varianceCosineScalar (v i)))
  refine ⟨by positivity,?_⟩
  calc
    _ <= (N : Real)⁻¹*((N : Real)*norm v^2) :=
      mul_le_mul_of_nonneg_left hCS (by positivity)
    _ = norm v^2 := by field_simp

theorem varianceCosineHessian_quadratic_lower {N : Nat} (hN : 0 < N)
    (a c : Real) (v : SourceFiniteConfiguration N 1) :
    min a (a+c)*norm v^2 <= inner Real v (varianceCosineHessian N a c v) := by
  have hq := varianceCosine_mean_direction_energy hN v
  have h1 := mul_le_mul_of_nonneg_right (min_le_left a (a+c)) (sub_nonneg.mpr hq.2)
  have h2 := mul_le_mul_of_nonneg_right (min_le_right a (a+c)) hq.1
  rw [varianceCosineHessian_quadratic]
  nlinarith

/-- The constant direction gives eigenvalue a+c; no square-root normalization
is hidden in the proof, since the nonzero vector has squared norm N. -/
theorem varianceCosineHessian_rayleigh_le_parallel {N : Nat} (hN : 0 < N) (a c : Real) :
    rayleighInf (varianceCosineHessian N a c) <= a+c := by
  let v : SourceFiniteConfiguration N 1 := WithLp.toLp 2 (fun _ => varianceCosinePoint 1)
  have hn : 0 < (N : Real) := by exact_mod_cast hN
  have hnorm : norm v^2 = (N : Real) := by
    simp [varianceCosine_configuration_norm_sq,v,varianceCosineScalar_point]
  have hsum : (∑ i : Fin N, varianceCosineScalar (v i)) = (N : Real) := by
    simp [v,varianceCosineScalar_point]
  have hval : inner Real v (varianceCosineHessian N a c v) = (a+c)*(N : Real) := by
    rw [varianceCosineHessian_quadratic,hnorm,hsum]
    field_simp <;> ring
  have h := rayleighInf_mul_norm_sq_le (varianceCosineHessian N a c) v
  rw [hnorm,hval] at h
  nlinarith

/-- Two distinct coordinates give a genuine centered direction. -/
theorem varianceCosine_centered_direction {N : Nat} (hN : 2 <= N) :
    exists v : SourceFiniteConfiguration N 1,
      norm v^2 = 2 ∧ (∑ i : Fin N, varianceCosineScalar (v i)) = 0 := by
  let i0 : Fin N := ⟨0,by omega⟩
  let i1 : Fin N := ⟨1,by omega⟩
  have h01 : i0 ≠ i1 := by intro h; have := congrArg Fin.val h; simp [i0,i1] at this
  let f : Fin N -> Real := fun i => (if i=i0 then 1 else 0)-(if i=i1 then 1 else 0)
  let v : SourceFiniteConfiguration N 1 := WithLp.toLp 2 (fun i => varianceCosinePoint (f i))
  have hscalar (i : Fin N) : varianceCosineScalar (v i) = f i := varianceCosineScalar_point _
  have hsq (i : Fin N) : (f i)^2 = (if i=i0 then 1 else 0)+(if i=i1 then 1 else 0) := by
    by_cases h0 : i=i0
    . subst i; simp [f,h01]
    . by_cases h1 : i=i1 <;> simp [f,h0,h1,h01.symm]
  refine ⟨v,?_,?_⟩
  . rw [varianceCosine_configuration_norm_sq]
    simp_rw [hscalar,hsq]
    norm_num [Finset.sum_add_distrib]
  . simp_rw [hscalar]
    simp [f,Finset.sum_sub_distrib]

theorem varianceCosineHessian_rayleigh_le_centered {N : Nat} (hN : 2 <= N) (a c : Real) :
    rayleighInf (varianceCosineHessian N a c) <= a := by
  obtain ⟨v,hnorm,hsum⟩ := varianceCosine_centered_direction hN
  have h := rayleighInf_mul_norm_sq_le (varianceCosineHessian N a c) v
  rw [varianceCosineHessian_quadratic,hnorm,hsum] at h
  nlinarith

/-- Exact lower spectral edge in the original nested PiLp particle space. -/
theorem varianceCosineHessian_rayleigh {N : Nat} (hN : 2 <= N) (a c : Real) :
    rayleighInf (varianceCosineHessian N a c) = min a (a+c) := by
  have hN0 : 0 < N := by omega
  letI : Nonempty (Fin N) := ⟨⟨0,hN0⟩⟩
  apply le_antisymm
  . exact le_min (varianceCosineHessian_rayleigh_le_centered hN a c)
      (varianceCosineHessian_rayleigh_le_parallel hN0 a c)
  . apply le_csInf (rayleighValues_nonempty (varianceCosineHessian N a c))
    rintro y ⟨v,hv,rfl⟩
    change norm v = 1 at hv
    simpa only [hv,one_pow,mul_one] using varianceCosineHessian_quadratic_lower hN0 a c v

/-- With one particle there is no centered eigenspace. -/
theorem varianceCosineHessian_rayleigh_one (a c : Real) :
    rayleighInf (varianceCosineHessian 1 a c) = a+c := by
  apply le_antisymm (varianceCosineHessian_rayleigh_le_parallel (by omega) a c)
  apply le_csInf (rayleighValues_nonempty (varianceCosineHessian 1 a c))
  rintro y ⟨v,hv,rfl⟩
  change norm v = 1 at hv
  change a + c <= inner Real v (varianceCosineHessian 1 a c v)
  have hn : (varianceCosineScalar (v 0))^2 = 1 := by
    simpa only [hv, one_pow, Fin.sum_univ_one] using (varianceCosine_configuration_norm_sq v).symm
  rw [varianceCosineHessian_quadratic]
  simp [hv,hn]

noncomputable def varianceCosineCurvature (a beta m : Real) : Real :=
  min a (-(varianceCosineCurvatureScale beta)*Real.cos (Real.pi*m))

noncomputable def varianceCosineRecoveryRate (a beta : Real) : Real :=
  min a (varianceCosineCurvatureScale beta/2)

theorem varianceCosineRecoveryRate_pos {a beta : Real} (ha : 0 < a) (hb : 0 < beta) :
    0 < varianceCosineRecoveryRate a beta :=
  lt_min ha (div_pos (varianceCosineCurvatureScale_pos hb) (by norm_num))

theorem varianceCosine_source_sampled_curvature {N : Nat} (hN : 2 <= N)
    (a beta : Real) (z : VarianceCosineHilbert) (Y : SourceFiniteConfiguration N 1) :
    rayleighInf (sampledMomentHessian varianceCosineEncodedFeature (varianceCosineObjective a beta) z Y) =
      varianceCosineCurvature a beta (varianceCosineDecode 0 z) := by
  rw [varianceCosine_source_sampled_hessian,varianceCosineHessian_rayleigh hN]
  unfold varianceCosineCurvature varianceCosineKernel varianceCosineCurvatureScale
  congr 1
  ring

theorem varianceCosine_population_sampled_curvature {N : Nat} (hN : 2 <= N)
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (R : Real) (hR : 0 <= R) (hU : ∀ᵐ u ∂ mu0, norm u <= R)
    (hmean : varianceCosineMean mu0 = 0) (a beta m r : Real) (Y : SourceFiniteConfiguration N 1) :
    rayleighInf (sampledMomentHessian varianceCosineEncodedFeature (varianceCosineObjective a beta)
      (integral (varianceCosinePopulation mu0 m r) varianceCosineEncodedFeature) Y) =
      varianceCosineCurvature a beta m := by
  rw [varianceCosine_source_sampled_curvature hN,
    varianceCosineDecode_integral _ (varianceCosinePopulation_memLp mu0 R hR hU m r) 0]
  change varianceCosineCurvature a beta (varianceCosineMean (varianceCosinePopulation mu0 m r)) = _
  rw [(varianceCosinePopulation_mean_variance mu0 R hR hU hmean m r).1]

theorem varianceCosineCurvature_lower (a beta m : Real) (ha : 0 <= a) (hb : 0 <= beta) :
    -varianceCosineCurvatureScale beta <= varianceCosineCurvature a beta m := by
  have hb0 : 0 <= varianceCosineCurvatureScale beta := by unfold varianceCosineCurvatureScale; positivity
  apply le_min (by linarith)
  have h := mul_le_mul_of_nonneg_left (Real.cos_le_one (Real.pi*m)) hb0
  linarith

theorem varianceCosineCurvature_abs (a beta m : Real) (ha : 0 <= a) (hb : 0 <= beta) :
    abs (varianceCosineCurvature a beta m) <= max a (varianceCosineCurvatureScale beta) := by
  apply abs_le.mpr
  constructor
  . exact (neg_le_neg (le_max_right a _)).trans (varianceCosineCurvature_lower a beta m ha hb)
  . exact (min_le_left a _).trans (le_max_left a _)

theorem varianceCosineCurvature_recovered (a beta m : Real) (hb : 0 <= beta)
    (hc : Real.cos (Real.pi*m) <= -(1/2 : Real)) :
    varianceCosineRecoveryRate a beta <= varianceCosineCurvature a beta m := by
  have hb0 : 0 <= varianceCosineCurvatureScale beta := by unfold varianceCosineCurvatureScale; positivity
  apply min_le_min le_rfl
  have h := mul_le_mul_of_nonneg_left hc hb0
  linarith

theorem varianceCosineCurvature_continuous (a beta : Real) :
    Continuous (varianceCosineCurvature a beta) := by
  unfold varianceCosineCurvature
  fun_prop

/-- The actually sampled curvature, not a free scalar surrogate, recovers. -/
theorem varianceCosine_mean_curvature_recovered
    (a beta T x rho t : Real) (hb : 0 < beta) (hr : 0 < rho)
    (hx : varianceCosineEscapeLanding rho x) (ht : t ∈ Icc 0 T)
    (hwait : varianceCosineRecoveryDelay (varianceCosineCurvatureScale beta) rho <= t) :
    varianceCosineRecoveryRate a beta <=
      varianceCosineCurvature a beta (varianceCosineMeanFlow beta T x t) :=
  varianceCosineCurvature_recovered a beta _ hb.le
    (varianceCosineMeanFlow_recovered_of_landing beta T x rho t hb hr hx ht hwait)
end PaperFormalization.Manuscript
