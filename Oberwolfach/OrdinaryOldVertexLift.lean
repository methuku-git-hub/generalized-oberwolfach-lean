module

public import Oberwolfach.OrdinaryExpansionDegrees

@[expose] public section

/-! Add disjoint unused row and hub labels to an old graph pair without
changing its degrees, balance or divisibility. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U X I : Type*}

def ordinaryOldRim (G : SimpleGraph V) : SimpleGraph (V⊕X) :=
  G.map (⟨Sum.inl,Sum.inl_injective⟩ : V ↪ V⊕X)

def ordinaryOldSpokes (H : V → U → Prop) : V⊕X → U⊕I → Prop
  | .inl a,.inl b => H a b
  | _,_ => False

theorem ordinaryOldRim_old_old (G : SimpleGraph V) (a b : V) :
    (ordinaryOldRim (X:=X) G).Adj (.inl a) (.inl b) ↔ G.Adj a b := by
  exact SimpleGraph.map_adj_apply (G:=G) (f:=(⟨Sum.inl,Sum.inl_injective⟩ : V ↪ V⊕X))

theorem ordinaryOldRim_old_private (G : SimpleGraph V) (a : V) (b : X) :
    (ordinaryOldRim G).Adj (.inl a) (.inr b) ↔ False := by
  simp [ordinaryOldRim,SimpleGraph.map_adj']

theorem ordinaryOldRim_private_any (G : SimpleGraph V) (a : X) (b : V⊕X) :
    (ordinaryOldRim G).Adj (.inr a) b ↔ False := by
  simp [ordinaryOldRim,SimpleGraph.map_adj']

section Finite
variable [Fintype V] [Fintype U] [Fintype X] [Fintype I]
    [DecidableEq V] [DecidableEq U] [DecidableEq X] [DecidableEq I]

theorem ordinaryOldRim_degree_old (G : SimpleGraph V) (a : V) :
    (ordinaryOldRim (X:=X) G).degree (.inl a)=G.degree a := by
  rw [graph_degree_indicator_sum,Fintype.sum_sum_type]
  simp only [ordinaryOldRim_old_old,ordinaryOldRim_old_private,naturalIndicator_false,Finset.sum_const_zero,add_zero]
  exact (graph_degree_indicator_sum G a).symm

theorem ordinaryOldRim_degree_private (G : SimpleGraph V) (a : X) :
    (ordinaryOldRim G).degree (.inr a)=0 := by
  rw [graph_degree_indicator_sum]
  simp only [ordinaryOldRim_private_any,naturalIndicator_false,Finset.sum_const_zero]

theorem ordinaryOldSpokes_row_old (H : V → U → Prop) (a : V) :
    (Finset.univ.filter (ordinaryOldSpokes (X:=X) (I:=I) H (.inl a))).card=
      (Finset.univ.filter (H a)).card := by
  simp only [card_filter_naturalIndicator,Fintype.sum_sum_type,ordinaryOldSpokes,
    naturalIndicator_false,Finset.sum_const_zero,add_zero]

theorem ordinaryOldSpokes_row_private (H : V → U → Prop) (a : X) :
    (Finset.univ.filter (ordinaryOldSpokes (I:=I) H (.inr a))).card=0 := by
  rw [card_filter_naturalIndicator,Fintype.sum_sum_type]
  simp [ordinaryOldSpokes,naturalIndicator]

theorem ordinaryOldSpokes_hub_old (H : V → U → Prop) (b : U) :
    (Finset.univ.filter (fun a => ordinaryOldSpokes (X:=X) (I:=I) H a (.inl b))).card=
      (Finset.univ.filter (fun a => H a b)).card := by
  simp only [card_filter_naturalIndicator,Fintype.sum_sum_type,ordinaryOldSpokes,
    naturalIndicator_false,Finset.sum_const_zero,add_zero]

theorem ordinaryOldSpokes_hub_private (H : V → U → Prop) (b : I) :
    (Finset.univ.filter (fun a => ordinaryOldSpokes (X:=X) H a (.inr b))).card=0 := by
  rw [card_filter_naturalIndicator,Fintype.sum_sum_type]
  simp [ordinaryOldSpokes,naturalIndicator]

theorem ordinaryOldPair_balance (G : SimpleGraph V) (H : V → U → Prop)
    (h : ∀ a,G.degree a=2*(Finset.univ.filter (H a)).card) :
    ∀ a,(ordinaryOldRim (X:=X) G).degree a=2*(Finset.univ.filter (ordinaryOldSpokes (I:=I) H a)).card := by
  intro a
  cases a with
  | inl a => rw [ordinaryOldRim_degree_old,ordinaryOldSpokes_row_old,h]
  | inr a => rw [ordinaryOldRim_degree_private,ordinaryOldSpokes_row_private]

theorem ordinaryOldPair_hub_divisibility (H : V → U → Prop) (r : ℕ)
    (h : ∀ b,r ∣ (Finset.univ.filter (fun a => H a b)).card) :
    ∀ b,r ∣ (Finset.univ.filter (fun a => ordinaryOldSpokes (X:=X) (I:=I) H a b)).card := by
  intro b
  cases b with
  | inl b => rw [ordinaryOldSpokes_hub_old];exact h b
  | inr b => rw [ordinaryOldSpokes_hub_private];exact dvd_zero r

end Finite
end Oberwolfach
