module

public import Oberwolfach.TupleRelationDeletionCounts
public import Oberwolfach.MarkedCommonPaths
public import Oberwolfach.MarkedCommonCycleTransfers

@[expose] public section

/-! Common marked cycles have c rim constraints and 2c spoke constraints.
Their degree-controlled deletion count is obtained on the actual fixed tuple
domain, before imposing the unchanged separation condition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U E K : Type*} {m : ℕ}

def commonMarkedCycleConstraint (R : Bool → V → V → Prop) (H : Bool → V → U → Prop)
    (u u' : U) (a : Fin (m+1)⊕(Bool×Fin (m+1))) (C : Fin (m+1) → V) : Prop :=
  Sum.elim (fun i=>R (decide (i=Fin.last m)) (C i) (C (finRotate (m+1) i)))
    (fun s=>H (markedPositionType s.2) (C s.2) (if s.1 then u' else u)) a

theorem commonMarkedCycleConstraint_all (R : Bool → V → V → Prop) (H : Bool → V → U → Prop)
    (u u' : U) (C : Fin (m+1) → V) :
    (∀ a,commonMarkedCycleConstraint R H u u' a C) ↔
      (∀ i,R (decide (i=Fin.last m)) (C i) (C (finRotate (m+1) i))) ∧
      MarkedHubCompatible (H false) (H true) C u ∧ MarkedHubCompatible (H false) (H true) C u' := by
  constructor
  · intro h
    refine ⟨fun i=>h (Sum.inl i),?_,?_⟩
    · apply (markedHubCompatible_iff_positions _ _ _ _).mpr
      intro i
      have hh := h (Sum.inr (false,i))
      dsimp only [commonMarkedCycleConstraint,Sum.elim_inr,Bool.false_eq_true,ite_false] at hh
      cases hi : markedPositionType i <;> simpa only [hi,Bool.false_eq_true,ite_false,ite_true] using hh
    · apply (markedHubCompatible_iff_positions _ _ _ _).mpr
      intro i
      have hh := h (Sum.inr (true,i))
      dsimp only [commonMarkedCycleConstraint,Sum.elim_inr,ite_true] at hh
      cases hi : markedPositionType i <;> simpa only [hi,Bool.false_eq_true,ite_false,ite_true] using hh
  · rintro ⟨hr,hu,hu'⟩ a
    cases a with
    | inl i => exact hr i
    | inr s =>
      rcases s with ⟨side,i⟩
      have h (v : U) (hv : MarkedHubCompatible (H false) (H true) C v) : H (markedPositionType i) (C i) v := by
        have hh := (markedHubCompatible_iff_positions _ _ _ _).mp hv i
        cases hi : markedPositionType i <;> simpa only [hi,Bool.false_eq_true,ite_false,ite_true] using hh
      cases side
      · exact h u hu
      · exact h u' hu'

theorem isMarkedCycleTuple_iff_relations
    (tail head : E → V) (ktail khead : K → V) (π : Equiv.Perm V) (b : ℕ)
    (C : Fin (m+1) → V) :
    IsMarkedCycleTuple tail head ktail khead m π b C ↔
      PermutationSeparated π b C ∧ ∀ i,
        (if i=Fin.last m then ∃ e,ktail e=C i ∧ khead e=C (finRotate (m+1) i)
          else ∃ e,tail e=C i ∧ head e=C (finRotate (m+1) i)) := by
  constructor
  · intro h
    refine ⟨h.1,fun i=>?_⟩
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simpa only [ite_true,finRotate_last] using h.2.2
    · simpa only [Fin.castSucc_ne_last,ite_false,finRotate_castSucc_eq_succ] using h.2.1 j
  · rintro ⟨hsep,h⟩
    refine ⟨hsep,?_,?_⟩
    · intro j
      simpa only [Fin.castSucc_ne_last,ite_false,finRotate_castSucc_eq_succ] using h j.castSucc
    · simpa only [ite_true,finRotate_last] using h (Fin.last m)

def commonMarkedCycleConstraintsEquiv
    (tail head : E → V) (ktail khead : K → V) (π : Equiv.Perm V) (b : ℕ)
    (H₀ Hₖ : V → U → Prop) (u u' : U) :
    CommonMarkedCycle tail head ktail khead m π b H₀ Hₖ u u' ≃
      {C : Fin (m+1) → V // PermutationSeparated π b C ∧
        ∀ a,commonMarkedCycleConstraint
          (fun j x y=>if j then ∃ e,ktail e=x ∧ khead e=y else ∃ e,tail e=x ∧ head e=y)
          (fun j=>if j then Hₖ else H₀) u u' a C} := by
  apply (Equiv.subtypeSubtypeEquivSubtypeInter
    (IsMarkedCycleTuple tail head ktail khead m π b)
    (fun C=>MarkedHubCompatible H₀ Hₖ C u ∧ MarkedHubCompatible H₀ Hₖ C u')).trans
  apply Equiv.subtypeEquivRight
  intro C
  rw [commonMarkedCycleConstraint_all,isMarkedCycleTuple_iff_relations]
  simp only [Bool.false_eq_true,ite_false,ite_true,decide_eq_true_eq]
  tauto

theorem commonMarkedCycle_constraint_loss [Fintype V] [DecidableEq V]
    (hm : 1≤m) (R R' : Bool → V → V → Prop) (H H' : Bool → V → U → Prop)
    (base : (Fin (m+1) → V) → Prop) (u u' : U) (d : ℝ)
    (hR : ∀ j x,(∑ y,bipAdj (fun x y=>R j x y ∧ ¬R' j x y) x y)≤d)
    (hH : ∀ j u,(∑ x,if H j x u ∧ ¬H' j x u then (1:ℝ) else 0)≤d) :
    (Fintype.card {C : Fin (m+1) → V // base C ∧ ∀ a,commonMarkedCycleConstraint R H u u' a C}:ℝ)-
      Fintype.card {C : Fin (m+1) → V // base C ∧ ∀ a,commonMarkedCycleConstraint R' H' u u' a C}≤
      3*((m:ℝ)+1)*d*(Fintype.card V:ℝ)^m := by
  have hb (a : Fin (m+1)⊕(Bool×Fin (m+1))) :
      (∑ C : Fin (m+1) → V,if commonMarkedCycleConstraint R H u u' a C ∧
        ¬commonMarkedCycleConstraint R' H' u u' a C then (1:ℝ) else 0)≤d*(Fintype.card V:ℝ)^m := by
    cases a with
    | inl i =>
      have hne : i≠finRotate (m+1) i := by
        letI : NeZero (m+1) := ⟨by omega⟩
        intro he
        rw [finRotate_apply] at he
        have h1 : (1 : Fin (m+1))=0 := add_left_cancel (show i+1=i+0 by simpa using he.symm)
        have hh := congrArg Fin.val h1
        norm_num [Fin.val_natCast,Nat.mod_eq_of_lt (show 1<m+1 by omega)] at hh
      have hh := tuple_relation_deletion_count (fun x y=>R (decide (i=Fin.last m)) x y ∧ ¬R' (decide (i=Fin.last m)) x y)
        i (finRotate (m+1) i) hne d (hR (decide (i=Fin.last m)))
      simp only [commonMarkedCycleConstraint,Sum.elim_inl,Fintype.card_fin,Nat.add_sub_cancel] at hh ⊢
      convert hh using 1 <;> congr!
    | inr s =>
      have hh := tuple_unary_deletion_count
        (fun x=>H (markedPositionType s.2) x (if s.1 then u' else u) ∧
          ¬H' (markedPositionType s.2) x (if s.1 then u' else u)) s.2 d (by convert hH (markedPositionType s.2) (if s.1 then u' else u) using 1 <;> congr!)
      simp only [commonMarkedCycleConstraint,Sum.elim_inr,Fintype.card_fin,Nat.add_sub_cancel] at hh ⊢
      convert hh using 1 <;> congr!
  have hh := finite_constraint_loss base (commonMarkedCycleConstraint R H u u')
    (commonMarkedCycleConstraint R' H' u u') (d*(Fintype.card V:ℝ)^m) hb
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at hh
  convert hh using 1 <;> ring

theorem represented_relation_lost_outdegree [Fintype V] [Fintype E]
    (tail head : E → V) (keep : E → Prop) (x : V) :
    (∑ y,bipAdj (fun x y=>(∃ e,tail e=x ∧ head e=y) ∧
      ¬(∃ e : {e // keep e},tail e.val=x ∧ head e.val=y)) x y)≤
      ∑ e,if ¬keep e ∧ tail e=x then (1:ℝ) else 0 := by
  calc
    _ ≤ ∑ y,∑ e,if ¬keep e ∧ tail e=x ∧ head e=y then (1:ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro y _
      by_cases h : (∃ e,tail e=x ∧ head e=y) ∧ ¬(∃ e : {e // keep e},tail e.val=x ∧ head e.val=y)
      · obtain ⟨e,he⟩ := h.1
        have hn : ¬keep e := fun hk=>h.2 ⟨⟨e,hk⟩,he⟩
        have hh := finite_exists_indicator_le_sum (fun e=>¬keep e ∧ tail e=x ∧ head e=y)
        have hex : ∃ e,¬keep e ∧ tail e=x ∧ head e=y := ⟨e,hn,he⟩
        simp only [hex,ite_true] at hh
        simp only [bipAdj]
        split_ifs with hh'
        · convert hh using 1 <;> congr!
      · simp only [bipAdj,h,ite_false]
        exact Finset.sum_nonneg (fun e _=>by split_ifs <;> norm_num)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : ¬keep e ∧ tail e=x
      · have hn := he.1
        have ht := he.2
        simp only [hn,ht,true_and,ite_true]
        simp
      · have hf (y : V) : ¬(¬keep e ∧ tail e=x ∧ head e=y) := fun h=>he ⟨h.1,h.2.1⟩
        simp only [he,hf,ite_false,Finset.sum_const_zero]

theorem represented_relation_lost_indegree [Fintype V] [Fintype E]
    (tail head : E → V) (keep : E → Prop) (y : V) :
    (∑ x,bipAdj (fun x y=>(∃ e,tail e=x ∧ head e=y) ∧
      ¬(∃ e : {e // keep e},tail e.val=x ∧ head e.val=y)) x y)≤
      ∑ e,if ¬keep e ∧ head e=y then (1:ℝ) else 0 := by
  have hh := represented_relation_lost_outdegree head tail keep y
  convert hh using 1 <;> simp only [bipAdj,and_comm] <;> congr!

theorem commonMarkedCycle_deletion_count [Fintype V] [Fintype E] [Fintype K] [DecidableEq V]
    (hm : 1≤m) (tail head : E → V) (ktail khead : K → V) (π : Equiv.Perm V) (b : ℕ)
    (PE : E → Prop) (PK : K → Prop) (H₀ Hₖ H₀' Hₖ' : V → U → Prop) (u u' : U) (d : ℝ)
    (hE : ∀ x,(∑ e,if ¬PE e ∧ tail e=x then (1:ℝ) else 0)≤d)
    (hK : ∀ x,(∑ e,if ¬PK e ∧ ktail e=x then (1:ℝ) else 0)≤d)
    (hH₀ : ∀ u,(∑ x,if H₀ x u ∧ ¬H₀' x u then (1:ℝ) else 0)≤d)
    (hHₖ : ∀ u,(∑ x,if Hₖ x u ∧ ¬Hₖ' x u then (1:ℝ) else 0)≤d) :
    (Fintype.card (CommonMarkedCycle tail head ktail khead m π b H₀ Hₖ u u'):ℝ)-
      Fintype.card (CommonMarkedCycle (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
        (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b H₀' Hₖ' u u')≤
      3*((m:ℝ)+1)*d*(Fintype.card V:ℝ)^m := by
  rw [Fintype.card_congr (commonMarkedCycleConstraintsEquiv tail head ktail khead π b H₀ Hₖ u u'),
    Fintype.card_congr (commonMarkedCycleConstraintsEquiv
      (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) π b H₀' Hₖ' u u')]
  apply commonMarkedCycle_constraint_loss hm
  · intro j x
    cases j
    · convert (represented_relation_lost_outdegree tail head PE x).trans (by convert hE x using 1 <;> congr!) using 1 <;> congr!
    · convert (represented_relation_lost_outdegree ktail khead PK x).trans (by convert hK x using 1 <;> congr!) using 1 <;> congr!
  · intro j u
    cases j
    · exact hH₀ u
    · exact hHₖ u

end Oberwolfach
