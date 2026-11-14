module

public import Oberwolfach.CyclicPathWeighting

@[expose] public section

/-! Fixed-point synchronization followed by exact summation over the omitted
interface. This is the path-weight assembly in the even cyclic-partite proof. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem sum_one_distinguished {I : Type*} [Fintype I] (i : I) (a b : ℝ) :
    (∑ c, if i = c then a else b) = a + (Fintype.card I - 1 : ℝ) * b := by
  have h (c : I) : (if i = c then a else b) = (if i = c then a - b else 0) + b := by
    split_ifs <;> ring
  simp_rw [h]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

theorem fractional_cycle_path_assembly_with_formula {k : ℕ} {X : Type*} [Fintype X]
    {P : Fin (k + 2) → Type*} [∀ i, Fintype (P i)]
    (m : Fin (k + 2) → X → ℝ) (B : ℝ)
    (hB : 0 < B) (hm : ∀ i x, 0 < m i x) (hms : ∀ i, ∑ x, m i x = B)
    (f : ∀ i, P i → X × X)
    (H : transportProduct m (finRotate (k + 2)) → Fin (k + 2) → X → X → ℝ)
    (hH : Continuous H)
    (hHm : ∀ Q i, H Q i ∈ transportMatrices (m i) (m (finRotate (k + 2) i)))
    (ρ R : transportProduct m (finRotate (k + 2)) → ∀ i, P i → ℝ)
    (hρ : ∀ Q i p, 0 ≤ ρ Q i p) (hR : ∀ Q i p, 0 ≤ R Q i p)
    (hρsum : ∀ Q i, ∑ p, ρ Q i p = B)
    (hRsum : ∀ Q i, ∑ p, R Q i p = B)
    (hρend : ∀ Q i x z, (∑ p, if f i p = (x, z) then ρ Q i p else 0) = Q.val i x z)
    (hRend : ∀ Q i x z, (∑ p, if f i p = (x, z) then R Q i p else 0) = H Q i x z) :
    ∃ Q : transportProduct m (finRotate (k + 2)), ∃ ω : (∀ i, P i) → ℝ,
      (∀ p, 0 ≤ ω p) ∧ (∑ p, ω p) = (k + 2 : ℝ) * B ∧
      (∀ i q, (∑ p, if p i = q then ω p else 0) =
        ρ Q i q + (k + 1 : ℝ) * R Q i q) ∧
      (∀ p, 0 < ω p → ∀ i,
        (f i (p i)).2 = (f (finRotate (k + 2) i) (p (finRotate (k + 2) i))).1) ∧
      (∀ i x z, Q.val i x z =
        walkTransport m (H Q) (finRotate (k + 2)) (finRotate (k + 2) i) (k + 1) z x) ∧
      (∀ p, (∀ i, (f i (p i)).2 =
          (f (finRotate (k + 2) i) (p (finRotate (k + 2) i))).1) →
        ω p = ∑ c, chainJoint m (H Q) (finRotate (k + 2))
          (finRotate (k + 2) c) (k + 1)
          (fun j => (f (cyclicChainOrder c j) (p (cyclicChainOrder c j))).1) *
          ∏ i, (if i = c then ρ Q i (p i) else R Q i (p i)) /
            (if i = c then Q.val c (f i (p i)).1 (f i (p i)).2
              else H Q i (f i (p i)).1 (f i (p i)).2)) := by
  obtain ⟨Q, hQ⟩ := complementary_transport_fixed_point m (finRotate (k + 2))
    (k + 1) (finRotate_complementary_closes k) B hB hm hms H hH hHm
  have hex (c : Fin (k + 2)) := cyclic_path_weighting_with_formula m (H Q) hm (hHm Q) c
    (Q.val c) (hQ c) B hB hms
    (fun i p => if i = c then ρ Q i p else R Q i p)
    (by intro i p; split_ifs; exact hρ Q i p; exact hR Q i p)
    (by intro i; by_cases hi : i = c <;> simp only [hi, ite_true, ite_false, hρsum, hRsum])
    f (by
      intro i x z
      by_cases hi : i = c
      · subst i
        simp only [ite_true]
        exact hρend Q c x z
      · simp only [hi, ite_false]
        exact hRend Q i x z)
  choose W hW htotal hmarg hclosed hformula using hex
  let ω (p : ∀ i, P i) := ∑ c, W c p
  refine ⟨Q, ω, ?_, ?_, ?_, ?_, hQ, ?_⟩
  · intro p
    exact Finset.sum_nonneg fun c _ => hW c p
  · dsimp only [ω]
    rw [Finset.sum_comm]
    simp only [htotal, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rfl
  · intro i q
    have hdist (p : ∀ i, P i) : (if p i = q then ω p else 0) =
        ∑ c, if p i = q then W c p else 0 := by
      unfold ω
      split_ifs <;> simp
    simp_rw [hdist]
    rw [Finset.sum_comm]
    simp_rw [hmarg]
    have hh := sum_one_distinguished i (ρ Q i q) (R Q i q)
    calc
      _ = ρ Q i q + (Fintype.card (Fin (k + 2)) - 1 : ℝ) * R Q i q := by
        convert hh using 1 <;>
          (apply Finset.sum_congr rfl; intro c _; split_ifs <;> rfl)
      _ = _ := by
        simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat]
        ring
  · intro p hp i
    by_contra hbad
    have hz (c : Fin (k + 2)) : W c p = 0 := by
      by_contra hne
      exact hbad (hclosed c p (lt_of_le_of_ne (hW c p) (Ne.symm hne)) i)
    have hzero : ω p = 0 := Finset.sum_eq_zero fun c _ => hz c
    rw [hzero] at hp
    exact (lt_irrefl 0) hp
  · intro p hp
    exact Finset.sum_congr rfl (fun c _ => hformula c p hp)

theorem fractional_cycle_path_assembly {k : ℕ} {X : Type*} [Fintype X]
    {P : Fin (k + 2) → Type*} [∀ i, Fintype (P i)]
    (m : Fin (k + 2) → X → ℝ) (B : ℝ)
    (hB : 0 < B) (hm : ∀ i x, 0 < m i x) (hms : ∀ i, ∑ x, m i x = B)
    (f : ∀ i, P i → X × X)
    (H : transportProduct m (finRotate (k + 2)) → Fin (k + 2) → X → X → ℝ)
    (hH : Continuous H)
    (hHm : ∀ Q i, H Q i ∈ transportMatrices (m i) (m (finRotate (k + 2) i)))
    (ρ R : transportProduct m (finRotate (k + 2)) → ∀ i, P i → ℝ)
    (hρ : ∀ Q i p, 0 ≤ ρ Q i p) (hR : ∀ Q i p, 0 ≤ R Q i p)
    (hρsum : ∀ Q i, ∑ p, ρ Q i p = B)
    (hRsum : ∀ Q i, ∑ p, R Q i p = B)
    (hρend : ∀ Q i x z, (∑ p, if f i p = (x, z) then ρ Q i p else 0) = Q.val i x z)
    (hRend : ∀ Q i x z, (∑ p, if f i p = (x, z) then R Q i p else 0) = H Q i x z) :
    ∃ Q : transportProduct m (finRotate (k + 2)), ∃ ω : (∀ i, P i) → ℝ,
      (∀ p, 0 ≤ ω p) ∧ (∑ p, ω p) = (k + 2 : ℝ) * B ∧
      (∀ i q, (∑ p, if p i = q then ω p else 0) =
        ρ Q i q + (k + 1 : ℝ) * R Q i q) ∧
      (∀ p, 0 < ω p → ∀ i,
        (f i (p i)).2 = (f (finRotate (k + 2) i) (p (finRotate (k + 2) i))).1) := by
  obtain ⟨Q, ω, hω, ht, hmarg, hs, _, _⟩ := fractional_cycle_path_assembly_with_formula
    m B hB hm hms f H hH hHm ρ R hρ hR hρsum hRsum hρend hRend
  exact ⟨Q, ω, hω, ht, hmarg, hs⟩

end Oberwolfach
