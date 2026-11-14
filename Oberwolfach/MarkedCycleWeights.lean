module

public import Oberwolfach.MarkedCycleIncidence
public import Oberwolfach.CopiedMarkedCapacities
public import Oberwolfach.SeparatedCapacityWeights

@[expose] public section

/-! Restricting the copied weights to the fixed family of marked cycles and
aggregating the ordinary positions. The lost load is counted once at each
ordinary position and once at the marked position. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem copied_marked_support_iff {V E K : Type*} [Fintype E] [Fintype K] [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V)
    (hinj : Function.Injective (fun e => (tail e,head e)))
    (hkinj : Function.Injective (fun e => (ktail e,khead e)))
    (m : ℕ) (f : Fin m → E → ℝ) (wK : K → ℝ)
    (hf : ∀ j e,0<f j e) (hwK : ∀ e,0<wK e) (C : Fin (m+1) → V) :
    (∀ i,0<copiedMarkedCapacity tail head ktail khead m f wK i (C i) (C (finRotate (m+1) i))) ↔
      (∀ j : Fin m,∃ e,tail e=C j.castSucc ∧ head e=C j.succ) ∧
        ∃ e,ktail e=C (Fin.last m) ∧ khead e=C 0 := by
  constructor
  · intro h
    constructor
    · intro j
      have hh := h j.castSucc
      rw [copiedMarkedCapacity_ordinary,finRotate_castSucc_eq_succ] at hh
      exact (occurrenceCapacityMatrix_pos_iff tail head hinj (f j) (hf j) _ _).mp hh
    · have hh := h (Fin.last m)
      rw [copiedMarkedCapacity_marked,finRotate_last] at hh
      exact (occurrenceCapacityMatrix_pos_iff ktail khead hkinj wK hwK _ _).mp hh
  · intro h i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [copiedMarkedCapacity_marked,finRotate_last]
      exact (occurrenceCapacityMatrix_pos_iff ktail khead hkinj wK hwK _ _).mpr h.2
    · rw [copiedMarkedCapacity_ordinary,finRotate_castSucc_eq_succ]
      exact (occurrenceCapacityMatrix_pos_iff tail head hinj (f j) (hf j) _ _).mpr (h.1 j)

theorem marked_cycle_weight_restriction {V E K : Type*}
    [Fintype V] [Fintype E] [Fintype K] [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V) (m : ℕ) (π : Equiv.Perm V) (b : ℕ)
    (u : (Fin (m+1) → V) → ℝ) (hu : ∀ C,0≤u C)
    (hs : ∀ C,0<u C → IsMarkedCycleTuple tail head ktail khead m π b C) :
    (∑ C : MarkedCycleTuple tail head ktail khead m π b,
      u C.val • markedCycleIncidence tail head ktail khead m C.val)=
      ∑ C,u C • markedCycleIncidence tail head ktail khead m C := by
  let S : Set (Fin (m+1) → V) := {C | IsMarkedCycleTuple tail head ktail khead m π b C}
  symm
  apply Finset.sum_congr_set S
    (fun C => u C • markedCycleIncidence tail head ktail khead m C)
    (fun C : S => u C.val • markedCycleIncidence tail head ktail khead m C.val)
  · intro C hC
    rfl
  · intro C hC
    have hz : u C=0 := le_antisymm (le_of_not_gt (fun hp => hC (hs C hp))) (hu C)
    simp only [hz,zero_smul]

theorem marked_cycle_weight_ordinary_load {V E K : Type*} [Fintype V] [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V) (m : ℕ)
    (u : (Fin (m+1) → V) → ℝ) (e : E) :
    (∑ C,u C*markedCycleIncidence tail head ktail khead m C (Sum.inl e))=
      ∑ j : Fin m,∑ C,if C j.castSucc=tail e ∧ C j.succ=head e then u C else 0 := by
  simp only [markedCycleIncidence,Sum.elim_inl,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro C _
  simp only [directedEdgeIndicator,mul_ite,mul_one,mul_zero,eq_comm]

theorem marked_cycle_weight_marked_load {V E K : Type*} [Fintype V] [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V) (m : ℕ)
    (u : (Fin (m+1) → V) → ℝ) (e : K) :
    (∑ C,u C*markedCycleIncidence tail head ktail khead m C (Sum.inr e))=
      ∑ C,if C (Fin.last m)=ktail e ∧ C 0=khead e then u C else 0 := by
  apply Finset.sum_congr rfl
  intro C _
  simp only [markedCycleIncidence,Sum.elim_inr,directedEdgeIndicator,mul_ite,mul_one,mul_zero,eq_comm]

set_option maxHeartbeats 1000000 in
theorem separated_marked_edge_loads {V E K : Type*}
    [Fintype V] [Nonempty V] [Fintype E] [Fintype K] [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V)
    (hinj : Function.Injective (fun e => (tail e,head e)))
    (hkinj : Function.Injective (fun e => (ktail e,khead e)))
    (m : ℕ) (hm : 2≤m) (π : Equiv.Perm V) (b : ℕ)
    (hsep : ∀ e,¬PermutationClose π b (tail e) (head e))
    (hksep : ∀ e,¬PermutationClose π b (ktail e) (khead e))
    (f : Fin m → E → ℝ) (w : E → ℝ) (wK : K → ℝ) (hsum : ∀ e,(∑ j,f j e)=w e)
    (u : (Fin (m+1) → V) → ℝ) (hu : ∀ C,0≤u C)
    (he : ∀ i x y,(∑ C,if C i=x ∧ C (finRotate (m+1) i)=y then u C else 0)=
      copiedMarkedCapacity tail head ktail khead m f wK i x y)
    (B : ℝ) (hB : 0≤B) (hupper : ∀ C,u C≤B/(Fintype.card V:ℝ)^(m-1)) :
    let loss := ((m+1:ℝ)^2*(2*b+1)*B)/(Fintype.card V:ℝ)
    (∀ e : E,|(∑ C,separatedWeight π b u C*markedCycleIncidence tail head ktail khead m C (Sum.inl e))-w e|≤m*loss) ∧
    (∀ e : K,|(∑ C,separatedWeight π b u C*markedCycleIncidence tail head ktail khead m C (Sum.inr e))-wK e|≤loss) := by
  let loss := ((m+1:ℝ)^2*(2*b+1)*B)/(Fintype.card V:ℝ)
  have ho (j : Fin m) (e : E) :
      f j e-loss≤(∑ C,if C j.castSucc=tail e ∧ C j.succ=head e then separatedWeight π b u C else 0) ∧
      (∑ C,if C j.castSucc=tail e ∧ C j.succ=head e then separatedWeight π b u C else 0)≤f j e := by
    have hh := separated_capacity_edge_bounds (by omega : 3≤m+1) π b
      (copiedMarkedCapacity tail head ktail khead m f wK) u hu
      (by
        intro i x y
        convert he i x y using 1
        apply Finset.sum_congr rfl
        intro C _
        split_ifs <;> rfl) B hB
      (by simpa only [show m+1-2=m-1 by omega] using hupper)
      j.castSucc (tail e) (head e) (hsep e)
    simpa only [copiedMarkedCapacity_ordinary,occurrenceCapacityMatrix_at_edge tail head hinj,
      finRotate_castSucc_eq_succ,Nat.cast_add,Nat.cast_one] using hh
  constructor
  · intro e
    rw [marked_cycle_weight_ordinary_load]
    have hlo := Finset.sum_le_sum (s := Finset.univ) (fun j _ => (ho j e).1)
    have hhi := Finset.sum_le_sum (s := Finset.univ) (fun j _ => (ho j e).2)
    simp only [Finset.sum_sub_distrib,hsum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hlo hhi
    rw [abs_le]
    constructor <;> linarith
  · intro e
    rw [marked_cycle_weight_marked_load]
    have hh := separated_capacity_edge_bounds (by omega : 3≤m+1) π b
      (copiedMarkedCapacity tail head ktail khead m f wK) u hu
      (by
        intro i x y
        convert he i x y using 1
        apply Finset.sum_congr rfl
        intro C _
        split_ifs <;> rfl) B hB
      (by simpa only [show m+1-2=m-1 by omega] using hupper)
      (Fin.last m) (ktail e) (khead e) (hksep e)
    simp only [copiedMarkedCapacity_marked,occurrenceCapacityMatrix_at_edge ktail khead hkinj,
      finRotate_last,Nat.cast_add,Nat.cast_one] at hh
    rw [abs_le]
    constructor <;> dsimp only [loss] at * <;> linarith

end Oberwolfach
