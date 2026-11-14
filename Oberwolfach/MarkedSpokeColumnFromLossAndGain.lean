module

public import Oberwolfach.MarkedOrdinarySpokeChangeGraph

@[expose] public section
/-! A fixed hub's change degree is controlled separately by its ordinary
spoke losses and gains; the marked spokes agree exactly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_spoke_column_from_loss_and_gain
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (H H':Bool→V→U→Prop) (hmark:∀x u,H true x u↔H' true x u)
    (loss gain:ℝ)
    (hLoss:∀u,((Finset.univ.filter (fun x=>H false x u∧¬H' false x u)).card:ℝ)≤loss)
    (hGain:∀u,((Finset.univ.filter (fun x=>H' false x u∧¬H false x u)).card:ℝ)≤gain):
    ∀u:U,((markedSpokeChangeGraph H H').degree (Sum.inr u):ℝ)≤loss+gain :=by
  obtain ⟨_,hcol⟩:=marked_spoke_change_graph_ordinary_only H H' hmark
  intro u
  rw [hcol]
  have hsub:(Finset.univ.filter (fun x=>¬(H false x u↔H' false x u)))⊆
      (Finset.univ.filter (fun x=>H false x u∧¬H' false x u))∪
        (Finset.univ.filter (fun x=>H' false x u∧¬H false x u)):=by
    intro x hx
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union] at hx ⊢
    tauto
  have hh:=(Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hh':((Finset.univ.filter (fun x=>¬(H false x u↔H' false x u))).card:ℝ)≤
      (Finset.univ.filter (fun x=>H false x u∧¬H' false x u)).card+
      (Finset.univ.filter (fun x=>H' false x u∧¬H false x u)).card:=by exact_mod_cast hh
  exact hh'.trans (add_le_add (hLoss u) (hGain u))
end Oberwolfach
