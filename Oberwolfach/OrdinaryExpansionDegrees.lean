module

public import Oberwolfach.OrdinaryFiniteExpansion

@[expose] public section

/-! Exact degree calculations for both parts of the finite expansion,
including the case of repeated formal pairs and formal rim loops. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E J W : Type*}
variable [Fintype V] [Fintype U] [Fintype E] [Fintype J] [Fintype W]
variable [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq J] [DecidableEq W]

theorem card_filter_naturalIndicator {A : Type*} [Fintype A] (p : A → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card=∑ a : A,naturalIndicator (p a) := by
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : p a <;> simp [naturalIndicator,h]

theorem ordinaryExpansionSpokes_degree_old_row (z : W) (v : J → V) (u : J → U) (a : V) :
    (Finset.univ.filter (ordinaryExpansionSpokes (E:=E) z v u (.inl a))).card=
      (Finset.univ.filter (fun j => a=v j)).card := by
  simp only [card_filter_naturalIndicator,Fintype.sum_sum_type,ordinaryExpansionSpokes,
    naturalIndicator_false,Finset.sum_const_zero,zero_add]

theorem ordinaryExpansionSpokes_degree_private_row (z : W) (v : J → V) (u : J → U)
    (i : E ⊕ J) (w : W) :
    (Finset.univ.filter (ordinaryExpansionSpokes z v u (.inr (i,w)))).card=1 := by
  rw [card_filter_naturalIndicator,Fintype.sum_sum_type]
  cases i with
  | inl e =>
    simp only [ordinaryExpansionSpokes,naturalIndicator_false,Finset.sum_const_zero,zero_add,
      naturalIndicator_sum_eq]
  | inr j =>
    by_cases hw : w=z
    · simp [ordinaryExpansionSpokes,hw,naturalIndicator]
    · simp [ordinaryExpansionSpokes,hw,naturalIndicator]

theorem ordinaryExpansionSpokes_degree_old_hub (z : W) (v : J → V) (u : J → U) (b : U) :
    (Finset.univ.filter (fun a => ordinaryExpansionSpokes (E:=E) z v u a (.inl b))).card=
      (Finset.univ.filter (fun j => b=u j)).card := by
  rw [card_filter_naturalIndicator,Fintype.sum_sum_type]
  simp only [ordinaryExpansionSpokes,naturalIndicator_false,Finset.sum_const_zero,zero_add,
    Fintype.sum_prod_type,Fintype.sum_sum_type]
  have h (j : J) (w : W) : naturalIndicator (w=z ∧ b=u j)=
      if b=u j then naturalIndicator (w=z) else 0 := by
    by_cases hb : b=u j <;> simp [naturalIndicator,hb]
  simp_rw [h,Finset.sum_ite_irrel,naturalIndicator_sum_eq,Finset.sum_const_zero]
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]

theorem ordinaryExpansionSpokes_degree_private_hub (z : W) (v : J → V) (u : J → U)
    (i : E ⊕ J) :
    (Finset.univ.filter (fun a => ordinaryExpansionSpokes z v u a (.inr i))).card=Fintype.card W := by
  rw [card_filter_naturalIndicator,Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type,Fintype.sum_sum_type]
  cases i with
  | inl e =>
    simp [ordinaryExpansionSpokes,naturalIndicator]
  | inr j =>
    have h (j' : J) (w : W) : naturalIndicator (w≠z ∧ (Sum.inr j : E ⊕ J)=Sum.inr j')=
        if j=j' then naturalIndicator (w≠z) else 0 := by
      by_cases hj : j=j' <;> simp [naturalIndicator,hj]
    simp only [ordinaryExpansionSpokes,naturalIndicator_false,Finset.sum_const_zero,zero_add]
    simp_rw [h,Finset.sum_ite_irrel]
    simp only [Finset.sum_const_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true,naturalIndicator_sum_eq]
    have hs : (∑ w : W,naturalIndicator (w=z))+(∑ w : W,naturalIndicator (w≠z))=Fintype.card W := by
      rw [← Finset.sum_add_distrib]
      calc
        _ = ∑ _w : W,1 := Finset.sum_congr rfl (by intro w _;by_cases hw : w=z <;> simp [naturalIndicator,hw])
        _ = _ := by simp
    rw [naturalIndicator_sum_eq] at hs
    simpa [naturalIndicator] using hs

theorem ordinaryExpansion_row_balance (C : SimpleGraph W) (z o : W) (hzo : C.Adj z o)
    (hC : C.IsRegularOfDegree 2) (x y : E → V) (v : J → V) (u : J → U)
    (hbal : ∀ a,(Finset.univ.filter (fun e => a=x e)).card+
      (Finset.univ.filter (fun e => a=y e)).card=2*(Finset.univ.filter (fun j => a=v j)).card) :
    ∀ a,(ordinaryExpansionRim C z o x y).degree a=
      2*(Finset.univ.filter (ordinaryExpansionSpokes z v u a)).card := by
  intro a
  cases a with
  | inl a => rw [ordinaryExpansionRim_degree_old C z o hzo.ne,ordinaryExpansionSpokes_degree_old_row,hbal]
  | inr p =>
    rcases p with ⟨i,w⟩
    rw [ordinaryExpansionRim_degree_private C z o hzo,ordinaryExpansionSpokes_degree_private_row,hC w]

theorem ordinaryExpansion_hub_divisibility (r : ℕ) (hW : Fintype.card W=r)
    (z : W) (v : J → V) (u : J → U)
    (hdiv : ∀ b,r ∣ (Finset.univ.filter (fun j => b=u j)).card) :
    ∀ b,r ∣ (Finset.univ.filter (fun a => ordinaryExpansionSpokes (E:=E) z v u a b)).card := by
  intro b
  cases b with
  | inl b => rw [ordinaryExpansionSpokes_degree_old_hub];exact hdiv b
  | inr i => rw [ordinaryExpansionSpokes_degree_private_hub,hW]

theorem ordinaryExpansion_order :
    Fintype.card (ExpansionRow V E J W)+Fintype.card (ExpansionHub U E J)=
      Fintype.card V+Fintype.card U+(Fintype.card E+Fintype.card J)*(Fintype.card W+1) := by
  simp only [ExpansionRow,ExpansionHub,Fintype.card_sum,Fintype.card_prod]
  ring

end Oberwolfach
