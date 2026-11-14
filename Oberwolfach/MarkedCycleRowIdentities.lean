module

public import Oberwolfach.MarkedWheels

@[expose] public section

/-! The exact incoming and outgoing identities of one canonical marked
cycle. These identities, rather than an informal balance assertion, will
supply the zero row sums in the wheel correction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem markedCycleIncidence_marked_head {V E K : Type*} [Fintype K] [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V)
    (hkinj : Function.Injective (fun e => (ktail e,khead e)))
    (m : ℕ) (π : Equiv.Perm V) (b : ℕ)
    (C : MarkedCycleTuple tail head ktail khead m π b) (v : V) :
    occurrenceSumLinear khead (fun e => markedCycleIncidence tail head ktail khead m C.val (Sum.inr e)) v=
      markedSpokeIndicator C.val true v := by
  exact directedEdgeIndicator_head ktail khead hkinj _ _ C.property.2.2 v

theorem markedCycleIncidence_outgoing {V E K : Type*} [Fintype E] [Fintype K] [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V)
    (hinj : Function.Injective (fun e => (tail e,head e)))
    (hkinj : Function.Injective (fun e => (ktail e,khead e)))
    (m : ℕ) (π : Equiv.Perm V) (b : ℕ)
    (C : MarkedCycleTuple tail head ktail khead m π b) (v : V) :
    occurrenceSumLinear (Sum.elim tail ktail) (markedCycleIncidence tail head ktail khead m C.val) v=
      markedSpokeIndicator C.val false v+markedSpokeIndicator C.val true v := by
  change (∑ e : E⊕K,if Sum.elim tail ktail e=v then markedCycleIncidence tail head ktail khead m C.val e else 0)=_
  simp only [Fintype.sum_sum_type,markedCycleIncidence,Sum.elim_inl,Sum.elim_inr]
  have ho : (∑ e : E,if tail e=v then
      (∑ i : Fin m,directedEdgeIndicator tail head (C.val i.castSucc) (C.val i.succ) e) else 0)=
      ∑ i : Fin m,occurrenceSumLinear tail (directedEdgeIndicator tail head (C.val i.castSucc) (C.val i.succ)) v := by
    calc
      _ = ∑ e : E,∑ i : Fin m,if tail e=v then
          directedEdgeIndicator tail head (C.val i.castSucc) (C.val i.succ) e else 0 := by
        apply Finset.sum_congr rfl
        intro e _
        split_ifs <;> simp
      _ = _ := Finset.sum_comm
  rw [ho]
  change (∑ i : Fin m,occurrenceSumLinear tail (directedEdgeIndicator tail head (C.val i.castSucc) (C.val i.succ)) v)+
    occurrenceSumLinear ktail (directedEdgeIndicator ktail khead (C.val (Fin.last m)) (C.val 0)) v=_
  simp only [directedEdgeIndicator_tail tail head hinj _ _ (C.property.2.1 _),
    directedEdgeIndicator_tail ktail khead hkinj _ _ C.property.2.2]
  have hfirst := Fin.sum_univ_castSucc (fun i : Fin (m+1) => if C.val i=v then (1:ℝ) else 0)
  have hlast := Fin.sum_univ_succ (fun i : Fin (m+1) => if C.val i=v then (1:ℝ) else 0)
  simp only [markedSpokeIndicator,Bool.false_eq_true,ite_false,ite_true]
  linarith

theorem marked_cycle_zero_on_close_arc {V E K : Type*} [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V) (m : ℕ) (hm : 1≤m)
    (π : Equiv.Perm V) (b : ℕ)
    (C : MarkedCycleTuple tail head ktail khead m π b) (e : E⊕K)
    (hc : PermutationClose π b (Sum.elim tail ktail e) (Sum.elim head khead e)) :
    markedCycleIncidence tail head ktail khead m C.val e=0 := by
  cases e with
  | inl e =>
    simp only [markedCycleIncidence,Sum.elim_inl]
    apply Finset.sum_eq_zero
    intro i _
    unfold directedEdgeIndicator
    apply if_neg
    intro hi
    have hne : i.castSucc≠i.succ := by
      intro he;have := congrArg Fin.val he;simp only [Fin.val_castSucc,Fin.val_succ] at this;omega
    exact C.property.1 i.castSucc i.succ hne (by simpa only [Sum.elim_inl,hi.1,hi.2] using hc)
  | inr e =>
    simp only [markedCycleIncidence,Sum.elim_inr,directedEdgeIndicator]
    apply if_neg
    intro hi
    have hne : (Fin.last m : Fin (m+1))≠0 := by
      intro he;have := congrArg Fin.val he;simp at this;omega
    exact C.property.1 (Fin.last m) 0 hne (by simpa only [Sum.elim_inr,hi.1,hi.2] using hc)

end Oberwolfach
