module

public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Tactic

@[expose] public section

/-! Reading the cyclic classes as a linear chain after omitting one interface. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem finRotate_iterate_val (k j : ℕ) (i : Fin (k + 2)) :
    ((finRotate (k + 2))^[j] i).val = (i.val + j) % (k + 2) := by
  induction j with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ j ih =>
    rw [Function.iterate_succ_apply', finRotate_apply]
    simp only [Fin.val_add, Fin.val_one, ih]
    rw [Nat.mod_add_mod, Nat.add_assoc]

def cyclicChainOrder {k : ℕ} (s : Fin (k + 2)) : Equiv.Perm (Fin (k + 2)) :=
  Equiv.addLeft (finRotate (k + 2) s)

theorem cyclicChainOrder_zero {k : ℕ} (s : Fin (k + 2)) :
    cyclicChainOrder s 0 = finRotate (k + 2) s := by
  simp [cyclicChainOrder]

theorem cyclicChainOrder_last {k : ℕ} (s : Fin (k + 2)) :
    cyclicChainOrder s (Fin.last (k + 1)) = s := by
  change finRotate (k + 2) s + Fin.last (k + 1) = s
  rw [finRotate_apply, ← Fin.neg_last (k + 1), add_assoc, neg_add_cancel, add_zero]

theorem cyclicChainOrder_succ {k : ℕ} (s : Fin (k + 2)) (i : Fin (k + 1)) :
    cyclicChainOrder s i.succ = finRotate (k + 2) (cyclicChainOrder s i.castSucc) := by
  change finRotate (k + 2) s + i.succ = finRotate (k + 2) (finRotate (k + 2) s + i.castSucc)
  rw [finRotate_apply (finRotate (k + 2) s + i.castSucc)]
  calc
    _ = finRotate (k + 2) s + (i.castSucc + 1) :=
      congrArg (fun a => finRotate (k + 2) s + a) (show i.castSucc + 1 = i.succ from Fin.coeSucc_eq_succ).symm
    _ = _ := (add_assoc _ _ _).symm

theorem cyclicChainOrder_iterate {k : ℕ} (s i : Fin (k + 2)) :
    cyclicChainOrder s i = (finRotate (k + 2))^[i.val] (finRotate (k + 2) s) := by
  apply Fin.ext
  rw [finRotate_iterate_val]
  rfl

theorem finRotate_complementary_closes (k : ℕ) (s : Fin (k + 2)) :
    (finRotate (k + 2))^[k + 1] (finRotate (k + 2) s) = s := by
  simpa only [Fin.val_last, cyclicChainOrder_last] using
    (cyclicChainOrder_iterate s (Fin.last (k + 1))).symm

theorem cyclicChainOrder_positions {k : ℕ} (s i : Fin (k + 2)) (hi : i ≠ s) :
    ∃ e : Fin (k + 1),
      (cyclicChainOrder s).symm i = e.castSucc ∧
      (cyclicChainOrder s).symm (finRotate (k + 2) i) = e.succ ∧
      (finRotate (k + 2))^[e.val] (finRotate (k + 2) s) = i := by
  let p := (cyclicChainOrder s).symm i
  have hlast : p ≠ Fin.last (k + 1) := by
    intro hp
    have hh := congrArg (cyclicChainOrder s) hp
    exact hi (by simpa only [p, Equiv.apply_symm_apply, cyclicChainOrder_last] using hh)
  have hp : p.val < k + 1 := by
    have hle := p.isLt
    have hn : p.val ≠ k + 1 := fun h => hlast (Fin.ext h)
    omega
  let e : Fin (k + 1) := ⟨p.val, hp⟩
  have hep : e.castSucc = p := Fin.ext rfl
  refine ⟨e, hep.symm, ?_, ?_⟩
  · apply (cyclicChainOrder s).injective
    rw [Equiv.apply_symm_apply, cyclicChainOrder_succ, hep]
    simp only [p, Equiv.apply_symm_apply]
  · calc
      _ = cyclicChainOrder s e.castSucc := (cyclicChainOrder_iterate s e.castSucc).symm
      _ = i := by
        rw [hep]
        exact (cyclicChainOrder s).apply_symm_apply i

end Oberwolfach
