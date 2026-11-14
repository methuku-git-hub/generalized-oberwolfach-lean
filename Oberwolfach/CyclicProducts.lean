module

public import Oberwolfach.CyclicCoordinates
public import Oberwolfach.ChainProduct

@[expose] public section

/-! Reindexing the complementary-chain products without changing or
duplicating any boundary vertex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem cyclicChainOrder_cast_ne {k : ℕ} (c : Fin (k + 2)) (e : Fin (k + 1)) :
    cyclicChainOrder c e.castSucc ≠ c := by
  intro h
  have hh := (cyclicChainOrder c).injective (h.trans (cyclicChainOrder_last c).symm)
  have hv := congrArg Fin.val hh
  simp only [Fin.val_castSucc, Fin.val_last] at hv
  omega

theorem cyclicChainOrder_internal_ne_first {k : ℕ}
    (c : Fin (k + 2)) (e : Fin k) :
    cyclicChainOrder c e.succ.castSucc ≠ finRotate (k + 2) c := by
  intro h
  have hh := (cyclicChainOrder c).injective (h.trans (cyclicChainOrder_zero c).symm)
  have hv := congrArg Fin.val hh
  simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_zero] at hv
  omega

theorem cyclic_complement_prod {k : ℕ} (c : Fin (k + 2)) (f : Fin (k + 2) → ℝ) :
    (∏ e : Fin (k + 1), f (cyclicChainOrder c e.castSucc)) =
      ∏ i ∈ Finset.univ.erase c, f i := by
  classical
  apply Finset.prod_bij (fun e _ => cyclicChainOrder c e.castSucc)
  · intro e _
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact cyclicChainOrder_cast_ne c e
  · intro a _ b _ hab
    have hh := (cyclicChainOrder c).injective hab
    exact Fin.ext (congrArg (fun z : Fin (k + 2) => z.val) hh)
  · intro i hi
    obtain ⟨e, he, _, _⟩ := cyclicChainOrder_positions c i (Finset.mem_erase.mp hi).1
    refine ⟨e, Finset.mem_univ _, ?_⟩
    rw [← he, Equiv.apply_symm_apply]
  · intro e _
    rfl

theorem cyclic_internal_prod {k : ℕ} (c : Fin (k + 2)) (f : Fin (k + 2) → ℝ) :
    (∏ e : Fin k, f (cyclicChainOrder c e.succ.castSucc)) =
      ∏ i ∈ (Finset.univ.erase c).erase (finRotate (k + 2) c), f i := by
  classical
  apply Finset.prod_bij (fun e _ => cyclicChainOrder c e.succ.castSucc)
  · intro e _
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨cyclicChainOrder_internal_ne_first c e, cyclicChainOrder_cast_ne c e.succ⟩
  · intro a _ b _ hab
    have hh := congrArg Fin.val ((cyclicChainOrder c).injective hab)
    apply Fin.ext
    simpa only [Fin.val_castSucc, Fin.val_succ, Nat.add_right_cancel_iff] using hh
  · intro i hi
    obtain ⟨hi0, hi⟩ := Finset.mem_erase.mp hi
    obtain ⟨e, he, _, _⟩ := cyclicChainOrder_positions c i (Finset.mem_erase.mp hi).1
    have he0 : e ≠ 0 := by
      intro hz
      have hh := congrArg (cyclicChainOrder c) he
      simp only [Equiv.apply_symm_apply, hz, Fin.castSucc_zero, cyclicChainOrder_zero] at hh
      exact hi0 hh
    obtain ⟨a, ha⟩ := Fin.exists_succ_eq_of_ne_zero he0
    refine ⟨a, Finset.mem_univ _, ?_⟩
    rw [ha, ← he, Equiv.apply_symm_apply]
  · intro e _
    rfl

theorem complementary_chain_product {k : ℕ} {X : Type*}
    (m : Fin (k + 2) → X → ℝ) (K : Fin (k + 2) → X → X → ℝ)
    (hm : ∀ i x, 0 < m i x) (c : Fin (k + 2)) (x : Fin (k + 2) → X) :
    chainJoint m K (finRotate (k + 2)) (finRotate (k + 2) c) (k + 1)
      (fun j => x (cyclicChainOrder c j)) =
      (∏ i ∈ Finset.univ.erase c, K i (x i) (x (finRotate (k + 2) i))) /
        ∏ j ∈ (Finset.univ.erase c).erase (finRotate (k + 2) c), m j (x j) := by
  rw [chainJoint_product m K (finRotate (k + 2)) hm]
  have hnum :
      (∏ t : Fin (k + 1),
        K ((finRotate (k + 2))^[t.val] (finRotate (k + 2) c))
          (x (cyclicChainOrder c t.castSucc)) (x (cyclicChainOrder c t.succ))) =
        ∏ t : Fin (k + 1), K (cyclicChainOrder c t.castSucc)
          (x (cyclicChainOrder c t.castSucc))
          (x (finRotate (k + 2) (cyclicChainOrder c t.castSucc))) := by
    apply Finset.prod_congr rfl
    intro t _
    have ht := cyclicChainOrder_iterate c t.castSucc
    simp only [Fin.val_castSucc] at ht
    rw [← ht, cyclicChainOrder_succ]
  have hden :
      (∏ t : Fin k,
        m ((finRotate (k + 2))^[t.val + 1] (finRotate (k + 2) c))
          (x (cyclicChainOrder c t.succ.castSucc))) =
        ∏ t : Fin k, m (cyclicChainOrder c t.succ.castSucc)
          (x (cyclicChainOrder c t.succ.castSucc)) := by
    apply Finset.prod_congr rfl
    intro t _
    have ht := cyclicChainOrder_iterate c t.succ.castSucc
    simp only [Fin.val_castSucc, Fin.val_succ] at ht
    rw [← ht]
  rw [hnum, hden,
    cyclic_complement_prod c (fun i => K i (x i) (x (finRotate (k + 2) i))),
    cyclic_internal_prod c (fun j => m j (x j))]

end Oberwolfach
