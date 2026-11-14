module

public import Oberwolfach.CyclicCoordinates
public import Oberwolfach.IntervalPathWeights

@[expose] public section

/-! The prescribed marginals are calculated from the interface graphs.
Balance at both types of vertex implies a common interface mass. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finRotate_invariant_constant {k : ℕ} {T : Type*}
    (f : Fin (k + 2) → T) (h : ∀ i, f (finRotate (k + 2) i) = f i)
    (i : Fin (k + 2)) : f i = f 0 := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    have hi := h i.castSucc
    rw [finRotate_apply, Fin.coeSucc_eq_succ] at hi
    exact hi.trans ih

def cyclicInterfaceDegree {I X Y : Type*} [Fintype Y]
    (L : I → X → Y → Prop) (i : I) (x : X) : ℝ :=
  (Finset.univ.filter (L i x)).card

theorem cyclic_interface_mass {k : ℕ} {X Y : Type*} [Fintype X] [Fintype Y]
    (L : Fin (k + 2) → X → Y → Prop) (R : Fin (k + 2) → Y → X → Prop)
    (hY : ∀ i y, (Finset.univ.filter (fun x => L i x y)).card =
      (Finset.univ.filter (R i y)).card)
    (hX : ∀ i z, (Finset.univ.filter (fun y => R i y z)).card =
      (Finset.univ.filter (L (finRotate (k + 2) i) z)).card)
    (i : Fin (k + 2)) :
    (∑ x, cyclicInterfaceDegree L i x) = ∑ x, cyclicInterfaceDegree L 0 x := by
  refine finRotate_invariant_constant (fun j => ∑ x, cyclicInterfaceDegree L j x) ?_ i
  intro j
  symm
  calc
    (∑ x, cyclicInterfaceDegree L j x) =
        ∑ x, ∑ y, interfaceCapacity (L j) x y := by
      simp only [interfaceCapacity_row, cyclicInterfaceDegree]
    _ = ∑ y, ∑ x, interfaceCapacity (L j) x y := Finset.sum_comm
    _ = ∑ y, ∑ z, interfaceCapacity (R j) y z := by
      simp_rw [interfaceCapacity_column, interfaceCapacity_row, hY]
    _ = ∑ z, ∑ y, interfaceCapacity (R j) y z := Finset.sum_comm
    _ = ∑ z, cyclicInterfaceDegree L (finRotate (k + 2) j) z := by
      simp only [interfaceCapacity_column, hX, cyclicInterfaceDegree]

theorem cyclic_interface_marginals {k : ℕ} {X Y : Type*}
    [Fintype X] [Fintype Y] [Nonempty X]
    (L : Fin (k + 2) → X → Y → Prop) (R : Fin (k + 2) → Y → X → Prop)
    (δ : ℝ) (hn : 0 < Fintype.card Y)
    (hthreshold : (k + 2 : ℝ) * Fintype.card Y ≤ (2 * (k + 2) - 1) * δ)
    (hdL : ∀ i x, δ ≤ (Finset.univ.filter (L i x)).card)
    (hY : ∀ i y, (Finset.univ.filter (fun x => L i x y)).card =
      (Finset.univ.filter (R i y)).card)
    (hX : ∀ i z, (Finset.univ.filter (fun y => R i y z)).card =
      (Finset.univ.filter (L (finRotate (k + 2) i) z)).card) :
    let m := fun i x => cyclicInterfaceDegree L i x / (k + 2 : ℝ)
    let B := ∑ x, m 0 x
    0 < B ∧ (∀ i x, 0 < m i x) ∧ (∀ i, ∑ x, m i x = B) := by
  dsimp only
  have hk : (0 : ℝ) < k + 2 := by positivity
  have hn' : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hn
  have hδ : 0 < δ := by
    have hprod := mul_pos hk hn'
    have hfac : (0 : ℝ) < 2 * (k + 2) - 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    exact pos_of_mul_pos_right (lt_of_lt_of_le hprod hthreshold) hfac.le
  have hm (i : Fin (k + 2)) (x : X) :
      0 < cyclicInterfaceDegree L i x / (k + 2 : ℝ) :=
    div_pos (lt_of_lt_of_le hδ (hdL i x)) hk
  refine ⟨Finset.sum_pos (fun x _ => hm 0 x) Finset.univ_nonempty, hm, ?_⟩
  intro i
  rw [← Finset.sum_div, ← Finset.sum_div, cyclic_interface_mass L R hY hX i]

end Oberwolfach
