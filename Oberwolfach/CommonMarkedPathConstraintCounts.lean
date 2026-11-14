module

public import Oberwolfach.InsertedTupleDeletionCounts
public import Oberwolfach.CommonMarkedCycleConstraintCounts

@[expose] public section

/-! Common paths are counted on their unchanged free-coordinate domain.
Only non-root spokes are constrained. The two root completions contribute
separate rim constraints, with no assumption that the four root spokes exist. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U E K : Type*} {m : ℕ}

def commonMarkedPathConstraint (R : Bool → V → V → Prop) (H : Bool → V → U → Prop)
    (i : Fin (m+1)) (v v' : V) (u u' : U)
    (a : (Bool×Fin (m+1))⊕(Bool×Fin m)) (z : Fin m → V) : Prop :=
  Sum.elim (fun s=>R (decide (s.2=Fin.last m))
      (Fin.insertNth (α:=fun _=>V) i (if s.1 then v' else v) z s.2)
      (Fin.insertNth (α:=fun _=>V) i (if s.1 then v' else v) z (finRotate (m+1) s.2)))
    (fun s=>H (markedPositionType (i.succAbove s.2)) (z s.2) (if s.1 then u' else u)) a

theorem commonMarkedPathConstraint_all (R : Bool → V → V → Prop) (H : Bool → V → U → Prop)
    (i : Fin (m+1)) (v v' : V) (u u' : U) (z : Fin m → V) :
    (∀ a,commonMarkedPathConstraint R H i v v' u u' a z) ↔
      (∀ j,R (decide (j=Fin.last m)) (Fin.insertNth (α:=fun _=>V) i v z j)
        (Fin.insertNth (α:=fun _=>V) i v z (finRotate (m+1) j))) ∧
      (∀ j,R (decide (j=Fin.last m)) (Fin.insertNth (α:=fun _=>V) i v' z j)
        (Fin.insertNth (α:=fun _=>V) i v' z (finRotate (m+1) j))) ∧
      ∀ k,H (markedPositionType (i.succAbove k)) (z k) u ∧
        H (markedPositionType (i.succAbove k)) (z k) u' := by
  constructor
  · intro h
    exact ⟨fun j=>h (Sum.inl (false,j)),fun j=>h (Sum.inl (true,j)),
      fun k=>⟨h (Sum.inr (false,k)),h (Sum.inr (true,k))⟩⟩
  · rintro ⟨h,h',hs⟩ a
    cases a with
    | inl s => rcases s with ⟨side,j⟩;cases side;exact h j;exact h' j
    | inr s => rcases s with ⟨side,k⟩;cases side;exact (hs k).1;exact (hs k).2

def commonMarkedPathConstraintsEquiv
    (tail head : E → V) (ktail khead : K → V) (π : Equiv.Perm V) (b : ℕ)
    (H₀ Hₖ : V → U → Prop) (i : Fin (m+1)) (v v' : V) (u u' : U) :
    CanonicalCommonMarkedPath tail head ktail khead m π b H₀ Hₖ i v v' u u' ≃
      {z : Fin m → V //
        (PermutationSeparated π b (Fin.insertNth (α:=fun _=>V) i v z) ∧
          PermutationSeparated π b (Fin.insertNth (α:=fun _=>V) i v' z)) ∧
        ∀ a,commonMarkedPathConstraint
          (fun j x y=>if j then ∃ e,ktail e=x ∧ khead e=y else ∃ e,tail e=x ∧ head e=y)
          (fun j=>if j then Hₖ else H₀) i v v' u u' a z} := by
  apply Equiv.subtypeEquivRight
  intro z
  rw [commonMarkedPathConstraint_all]
  simp only [isMarkedCycleTuple_iff_relations,decide_eq_true_eq,ite_apply]
  tauto

theorem commonMarkedPath_constraint_loss [Fintype V] [DecidableEq V]
    (hm : 1≤m) (R R' : Bool → V → V → Prop) (H H' : Bool → V → U → Prop)
    (base : (Fin m → V) → Prop) (i : Fin (m+1)) (v v' : V) (u u' : U) (d : ℝ)
    (hRout : ∀ j x,(∑ y,bipAdj (fun x y=>R j x y ∧ ¬R' j x y) x y)≤d)
    (hRin : ∀ j y,(∑ x,bipAdj (fun x y=>R j x y ∧ ¬R' j x y) x y)≤d)
    (hH : ∀ j u,(∑ x,if H j x u ∧ ¬H' j x u then (1:ℝ) else 0)≤d) :
    (Fintype.card {z : Fin m → V // base z ∧ ∀ a,commonMarkedPathConstraint R H i v v' u u' a z}:ℝ)-
      Fintype.card {z : Fin m → V // base z ∧ ∀ a,commonMarkedPathConstraint R' H' i v v' u u' a z}≤
      4*((m:ℝ)+1)*d*(Fintype.card V:ℝ)^(m-1) := by
  have hd : 0≤d := le_trans (Finset.sum_nonneg (fun y _=>by unfold bipAdj;positivity)) (hRout false v)
  have hb (a : (Bool×Fin (m+1))⊕(Bool×Fin m)) :
      (∑ z : Fin m → V,if commonMarkedPathConstraint R H i v v' u u' a z ∧
        ¬commonMarkedPathConstraint R' H' i v v' u u' a z then (1:ℝ) else 0)≤
      d*(Fintype.card V:ℝ)^(m-1) := by
    cases a with
    | inl s =>
      have hne : s.2≠finRotate (m+1) s.2 := by
        intro he
        rw [finRotate_apply] at he
        have h1 : (1 : Fin (m+1))=0 := add_left_cancel (show s.2+1=s.2+0 by simpa using he.symm)
        have hh := congrArg Fin.val h1
        norm_num [Fin.val_natCast,Nat.mod_eq_of_lt (show 1<m+1 by omega)] at hh
      have hh := inserted_tuple_relation_deletion_count
        (fun x y=>R (decide (s.2=Fin.last m)) x y ∧ ¬R' (decide (s.2=Fin.last m)) x y)
        i s.2 (finRotate (m+1) s.2) hne (if s.1 then v' else v) d
        (hRout (decide (s.2=Fin.last m))) (hRin (decide (s.2=Fin.last m)))
      simp only [commonMarkedPathConstraint,Sum.elim_inl] at hh ⊢
      convert hh using 1 <;> congr!
    | inr s =>
      have hh := tuple_unary_deletion_count
        (fun x=>H (markedPositionType (i.succAbove s.2)) x (if s.1 then u' else u) ∧
          ¬H' (markedPositionType (i.succAbove s.2)) x (if s.1 then u' else u)) s.2 d
        (by convert hH (markedPositionType (i.succAbove s.2)) (if s.1 then u' else u) using 1 <;> congr!)
      simp only [commonMarkedPathConstraint,Sum.elim_inr,Fintype.card_fin] at hh ⊢
      convert hh using 1 <;> congr!
  have hh := finite_constraint_loss base (commonMarkedPathConstraint R H i v v' u u')
    (commonMarkedPathConstraint R' H' i v v' u u') (d*(Fintype.card V:ℝ)^(m-1)) hb
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,
    Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at hh
  have hbound : ((2:ℝ)*(m+1)+2*m)*(d*(Fintype.card V:ℝ)^(m-1))≤
      4*((m:ℝ)+1)*d*(Fintype.card V:ℝ)^(m-1) := by
    have hn : 0≤d*(Fintype.card V:ℝ)^(m-1) := by positivity
    nlinarith
  exact hh.trans hbound

theorem commonMarkedPath_deletion_count [Fintype V] [Fintype E] [Fintype K] [DecidableEq V]
    (hm : 1≤m) (tail head : E → V) (ktail khead : K → V) (π : Equiv.Perm V) (b : ℕ)
    (PE : E → Prop) (PK : K → Prop) (H₀ Hₖ H₀' Hₖ' : V → U → Prop)
    (i : Fin (m+1)) (v v' : V) (u u' : U) (d : ℝ)
    (hEout : ∀ x,(∑ e,if ¬PE e ∧ tail e=x then (1:ℝ) else 0)≤d)
    (hEin : ∀ x,(∑ e,if ¬PE e ∧ head e=x then (1:ℝ) else 0)≤d)
    (hKout : ∀ x,(∑ e,if ¬PK e ∧ ktail e=x then (1:ℝ) else 0)≤d)
    (hKin : ∀ x,(∑ e,if ¬PK e ∧ khead e=x then (1:ℝ) else 0)≤d)
    (hH₀ : ∀ u,(∑ x,if H₀ x u ∧ ¬H₀' x u then (1:ℝ) else 0)≤d)
    (hHₖ : ∀ u,(∑ x,if Hₖ x u ∧ ¬Hₖ' x u then (1:ℝ) else 0)≤d) :
    (Fintype.card (CanonicalCommonMarkedPath tail head ktail khead m π b H₀ Hₖ i v v' u u'):ℝ)-
      Fintype.card (CanonicalCommonMarkedPath (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
        (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b H₀' Hₖ' i v v' u u')≤
      4*((m:ℝ)+1)*d*(Fintype.card V:ℝ)^(m-1) := by
  rw [Fintype.card_congr (commonMarkedPathConstraintsEquiv tail head ktail khead π b H₀ Hₖ i v v' u u'),
    Fintype.card_congr (commonMarkedPathConstraintsEquiv
      (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) π b H₀' Hₖ' i v v' u u')]
  have hh := commonMarkedPath_constraint_loss hm
    (fun j x y=>if j then ∃ e,ktail e=x ∧ khead e=y else ∃ e,tail e=x ∧ head e=y)
    (fun j x y=>if j then ∃ e : {e // PK e},ktail e.val=x ∧ khead e.val=y
      else ∃ e : {e // PE e},tail e.val=x ∧ head e.val=y)
    (fun j=>if j then Hₖ else H₀) (fun j=>if j then Hₖ' else H₀')
    (fun z=>(PermutationSeparated π b (Fin.insertNth (α:=fun _=>V) i v z) ∧
      PermutationSeparated π b (Fin.insertNth (α:=fun _=>V) i v' z)))
    i v v' u u' d (by
    intro j x
    cases j
    · convert (represented_relation_lost_outdegree tail head PE x).trans
        (by convert hEout x using 1 <;> congr!) using 1 <;> congr!
    · convert (represented_relation_lost_outdegree ktail khead PK x).trans
        (by convert hKout x using 1 <;> congr!) using 1 <;> congr!
    ) (by
    intro j x
    cases j
    · convert (represented_relation_lost_indegree tail head PE x).trans
        (by convert hEin x using 1 <;> congr!) using 1 <;> congr!
    · convert (represented_relation_lost_indegree ktail khead PK x).trans
        (by convert hKin x using 1 <;> congr!) using 1 <;> congr!
    ) (by
    intro j u
    cases j
    · exact hH₀ u
    · exact hHₖ u)
  convert hh using 1 <;> congr!

end Oberwolfach
