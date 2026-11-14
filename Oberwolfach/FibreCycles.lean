module

public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.Tactic

@[expose] public section

/-! A permutation that is one cycle on each fibre of a finite partition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem fibre_cycles {V K : Type*} [Fintype V] [DecidableEq K] (cell : V → K) :
    ∃ π : Equiv.Perm V, (∀ x, cell (π x) = cell x) ∧
      ∀ x k, (π ^ k) x = x ↔
        (Finset.univ.filter (fun y => cell y = cell x)).card ∣ k := by
  classical
  let A (c : K) : Finset V := Finset.univ.filter (fun x => cell x = c)
  have hex : ∀ c : K, ∃ p : Equiv.Perm V, p.IsCycleOn (A c) ∧ p.support ⊆ A c :=
    fun c => (A c).exists_cycleOn
  choose p hp using hex
  have hx (x : V) : x ∈ A (cell x) := by simp [A]
  have hforward (x : V) : cell (p (cell x) x) = cell x :=
    (Finset.mem_filter.mp ((hp (cell x)).1.1.mapsTo (hx x))).2
  have hbackward (x : V) : cell ((p (cell x)).symm x) = cell x :=
    (Finset.mem_filter.mp ((hp (cell x)).1.inv.1.mapsTo (hx x))).2
  let π : Equiv.Perm V := {
    toFun := fun x => p (cell x) x
    invFun := fun x => (p (cell x)).symm x
    left_inv := fun x => by
      dsimp only
      rw [hforward]
      exact (p (cell x)).symm_apply_apply x
    right_inv := fun x => by
      dsimp only
      rw [hbackward]
      exact (p (cell x)).apply_symm_apply x }
  have hpow (x : V) (k : ℕ) : (π ^ k) x = (p (cell x) ^ k) x := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih]
      change p (cell ((p (cell x) ^ k) x)) ((p (cell x) ^ k) x) =
        p (cell x) ((p (cell x) ^ k) x)
      have hm := (hp (cell x)).1.1.mapsTo.perm_pow k (hx x)
      rw [(Finset.mem_filter.mp hm).2]
  refine ⟨π, hforward, ?_⟩
  intro x k
  rw [hpow]
  exact (hp (cell x)).1.pow_apply_eq (hx x)

end Oberwolfach
