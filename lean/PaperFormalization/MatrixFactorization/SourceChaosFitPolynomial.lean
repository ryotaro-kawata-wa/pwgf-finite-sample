import PaperFormalization.MatrixFactorization.SourceChaosCoefficients
import PaperFormalization.MatrixFactorization.ActiveC2RetractionCurvature

/-! # MF43: the printed finite coefficient loss as an ambient polynomial

The polynomial below is built from the source's actual contraction sum.
Its Gaussian Parseval identity concerns the reconstructed chaos expansion.
Equality with the original product of features still requires the general
Hermite product formula and is not introduced as an assumption here.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

/-- All possibly nonzero output degrees of the finite activation. -/
def activeChaosDegrees (O : Finset Nat) : Finset Nat :=
  Finset.range (2 * activationOrder O + 1)

/-- The source coefficient evaluated at its symmetric/antisymmetric raw
coordinates, including directions away from the antisymmetric branch. -/
noncomputable def sourceActiveCoefficient {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (q : Nat) (X : ActiveMomentCoordinates d O) :
    SymmetricHermiteCoefficient d (Fin h × Fin h) q :=
  activeChaosCoefficient O a q (X 0 + X 1) (X 0 - X 1)

theorem sourceActiveCoefficient_contDiff {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (q : Nat) :
    ContDiff Real ⊤ (sourceActiveCoefficient (d := d) O a q) := by
  letI : NormedSpace Real (ActiveMomentCoordinates d O) := PiLp.normedSpace 2 Real _
  have hp : ContDiff Real ⊤ (fun X : ActiveMomentCoordinates d O => X 0 + X 1) :=
    (PiLp.proj (𝕜 := Real) 2 (fun _ : Fin 2 => ActiveMomentSpace d O) 0).contDiff.add
      (PiLp.proj (𝕜 := Real) 2 (fun _ : Fin 2 => ActiveMomentSpace d O) 1).contDiff
  have hm : ContDiff Real ⊤ (fun X : ActiveMomentCoordinates d O => X 0 - X 1) :=
    (PiLp.proj (𝕜 := Real) 2 (fun _ : Fin 2 => ActiveMomentSpace d O) 0).contDiff.sub
      (PiLp.proj (𝕜 := Real) 2 (fun _ : Fin 2 => ActiveMomentSpace d O) 1).contDiff
  exact (activeChaosCoefficient_contDiff (d := d) O a q).comp (hp.prodMk hm)

/-- The source's literal one-half sum of full output/spatial HS residual
squares. It is defined on the full original active Hilbert space. -/
noncomputable def sourceCoefficientFitPolynomial {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (teacher : ActiveMomentSpace d O) (X : ActiveMomentCoordinates d O) : Real :=
  (1 / 2 : Real) * ∑ q ∈ activeChaosDegrees O,
    ‖sourceActiveCoefficient O a q X - activeChaosCoefficient O a q teacher teacher‖ ^ 2

/-- The explicit source coefficient loss is C-infinity on the ambient space. -/
theorem sourceCoefficientFitPolynomial_contDiff {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (teacher : ActiveMomentSpace d O) :
    ContDiff Real ⊤ (sourceCoefficientFitPolynomial O a teacher) := by
  have hc : ContDiff Real ⊤ (fun _ : ActiveMomentCoordinates d O => (1 / 2 : Real)) :=
    contDiff_const
  apply hc.mul
  apply ContDiff.sum
  intro q hq
  exact ((sourceActiveCoefficient_contDiff (d := d) O a q).sub contDiff_const).norm_sq Real

theorem sourceCoefficientFitPolynomial_nonneg {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (teacher : ActiveMomentSpace d O) (X : ActiveMomentCoordinates d O) :
    0 ≤ sourceCoefficientFitPolynomial O a teacher X := by
  unfold sourceCoefficientFitPolynomial
  positivity

/-- The student and teacher coefficient blocks agree at the actual teacher
coordinates `(S,A) = (teacher,0)`. -/
theorem sourceCoefficientFitPolynomial_teacher {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (teacher : ActiveMomentSpace d O) :
    sourceCoefficientFitPolynomial O a teacher (WithLp.toLp 2 ![teacher, 0]) = 0 := by
  simp [sourceCoefficientFitPolynomial, sourceActiveCoefficient]

/-- Coefficients outside the finite degree set really vanish. -/
theorem sourceActiveCoefficient_eq_zero_of_not_mem {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (q : Nat) (hq : q ∉ activeChaosDegrees O)
    (X : ActiveMomentCoordinates d O) : sourceActiveCoefficient O a q X = 0 := by
  have h : 2 * activationOrder O < q := by
    simpa only [activeChaosDegrees, Finset.mem_range, not_lt, Nat.add_one_le_iff] using hq
  simp [sourceActiveCoefficient, activeChaosCoefficient_eq_zero_of_degree_lt O a q h]

/-- This is the polynomial reconstructed from the explicit source coefficients.
The separate original-feature product identity is deliberately not hidden
in its definition. -/
noncomputable def sourceChaosMatrixPolynomial {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (X Y : ActiveMomentSpace d O) (z : Weight d) :
    EuclideanSpace Real (Fin h × Fin h) :=
  tensorHermiteVectorPolynomial (activeChaosDegrees O)
    (fun q ij => (activeChaosCoefficient O a q X Y ij).val) z

/-- The reconstructed source residual has a genuine squared Gaussian
integral; the total integral convention is not used to bypass this duty. -/
theorem sourceChaosMatrixPolynomial_residual_integrable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (X Y U V : ActiveMomentSpace d O) :
    Integrable (fun z : Weight d =>
      ‖sourceChaosMatrixPolynomial O a X Y z - sourceChaosMatrixPolynomial O a U V z‖ ^ 2)
      (stdGaussian (Weight d)) := by
  let T := fun q => activeChaosCoefficient O a q X Y - activeChaosCoefficient O a q U V
  have he (z : Weight d) :
      sourceChaosMatrixPolynomial O a X Y z - sourceChaosMatrixPolynomial O a U V z =
        tensorHermiteVectorPolynomial (activeChaosDegrees O) (fun q ij => (T q ij).val) z := by
    apply PiLp.ext
    intro ij
    change (∑ q ∈ activeChaosDegrees O,
        inner Real (normalizedHermiteTensor d q z).val (activeChaosCoefficient O a q X Y ij).val) -
      (∑ q ∈ activeChaosDegrees O,
        inner Real (normalizedHermiteTensor d q z).val (activeChaosCoefficient O a q U V ij).val) = _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    exact (inner_sub_right _ _ _).symm
  simp_rw [he]
  exact tensorHermiteVectorPolynomial_sq_integrable _ _

/-- The exact one-half residual Parseval identity is proved for the source
coefficient reconstruction, with the original Frobenius/tensor norm. -/
theorem sourceCoefficientFitPolynomial_parseval {d h : Nat} (pole : UnitSphere d)
    (O : Finset Nat) (a : Nat → Weight h) (teacher : ActiveMomentSpace d O)
    (X : ActiveMomentCoordinates d O) :
    sourceCoefficientFitPolynomial O a teacher X =
      (1 / 2 : Real) * ∫ z : Weight d,
        ‖sourceChaosMatrixPolynomial O a (X 0 + X 1) (X 0 - X 1) z -
          sourceChaosMatrixPolynomial O a teacher teacher z‖ ^ 2 ∂stdGaussian (Weight d) := by
  unfold sourceChaosMatrixPolynomial sourceCoefficientFitPolynomial sourceActiveCoefficient
  rw [symmetricHermiteCoefficient_residual_parseval pole]

end PaperFormalization.MatrixFactorization
