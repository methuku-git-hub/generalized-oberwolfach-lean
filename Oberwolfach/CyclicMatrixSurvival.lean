module

public import Oberwolfach.RegularCyclicMatrixWeights
public import Oberwolfach.CommonEvents

@[expose] public section

/-! Survival estimates for the specified edges of one transversal cycle.
Only marginal deletion bounds are used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def cyclicMatrixEndpoints {k : ℕ} {X : Type*} (v : Fin (k + 2) → X × X) :
    Fin (k + 2) ⊕ Fin (k + 2) → X × X
  | Sum.inl i => v i
  | Sum.inr i => ((v i).2, (v (finRotate (k + 2) i)).1)

theorem cyclicMatrixTupleValid_iff {k : ℕ} {X : Type*}
    (M : (Fin (k + 2) ⊕ Fin (k + 2)) → X → X → ℕ)
    (v : Fin (k + 2) → X × X) : CyclicMatrixTupleValid M v ↔
      ∀ i, 0 < M i (cyclicMatrixEndpoints v i).1 (cyclicMatrixEndpoints v i).2 := by
  constructor
  · intro h i; cases i with
    | inl i => exact (h i).1
    | inr i => exact (h i).2
  · intro h i; exact ⟨h (Sum.inl i), h (Sum.inr i)⟩

theorem cyclicMatrix_tuple_survival {Ω X : Type*} [Fintype Ω] {k : ℕ}
    (μ : FiniteLaw Ω)
    (M : (Fin (k + 2) ⊕ Fin (k + 2)) → X → X → ℕ)
    (R : Ω → (Fin (k + 2) ⊕ Fin (k + 2)) → X → X → ℕ)
    (p : ℝ)
    (hp : ∀ i x y, 0 < M i x y → μ.probability (fun ω => R ω i x y = 0) ≤ p)
    (v : Fin (k + 2) → X × X) (hv : CyclicMatrixTupleValid M v) :
    1 - (2 * (k + 2 : ℝ)) * p ≤ μ.probability (fun ω => CyclicMatrixTupleValid (R ω) v) := by
  have h := finiteLaw_common_event_lower μ Finset.univ
    (fun i ω => R ω i (cyclicMatrixEndpoints v i).1 (cyclicMatrixEndpoints v i).2 = 0)
    (fun _ => p)
    (fun i _ => hp i _ _ ((cyclicMatrixTupleValid_iff M v).mp hv i))
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_ofNat, Finset.mem_univ, forall_const,
    ← Nat.pos_iff_ne_zero, ← cyclicMatrixTupleValid_iff, two_mul] using h

theorem finiteLaw_binary_mean {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (R : Ω → ℕ) (hR : ∀ ω, R ω ≤ 1) :
    μ.expectation (fun ω => (R ω : ℝ)) = μ.probability (fun ω => 0 < R ω) := by
  unfold FiniteLaw.expectation FiniteLaw.probability
  apply Finset.sum_congr rfl
  intro ω _
  have h := hR ω
  by_cases hz : R ω = 0
  · simp [hz]
  · have h1 : R ω = 1 := by omega
    simp [h1]

theorem finiteLaw_retained_binary_mean {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (M : ℕ) (hM : M ≤ 1) (R : Ω → ℕ)
    (hR : ∀ ω, R ω ≤ M) (p : ℝ)
    (hp : 0 < M → μ.probability (fun ω => R ω = 0) ≤ p) :
    (1 - p) * M ≤ μ.expectation (fun ω => (R ω : ℝ)) ∧
      μ.expectation (fun ω => (R ω : ℝ)) ≤ M := by
  constructor
  · by_cases hz : M = 0
    · have hz' : ∀ ω, R ω = 0 := fun ω => Nat.le_zero.mp (hz ▸ hR ω)
      simp only [hz, Nat.cast_zero, mul_zero, hz', finiteLaw_expectation_const, le_refl]
    · have h1 : M = 1 := by omega
      rw [finiteLaw_binary_mean μ R (fun ω => (hR ω).trans hM), h1, Nat.cast_one, mul_one]
      have he := finiteLaw_probability_compl μ (fun ω => R ω = 0)
      simp only [← Nat.pos_iff_ne_zero] at he
      linarith [hp (by omega)]
  · have h := finiteLaw_expectation_mono μ (fun ω => (R ω : ℝ)) (fun _ => (M : ℝ))
      (fun ω => by exact_mod_cast hR ω)
    simpa only [finiteLaw_expectation_const] using h

end Oberwolfach
