module

public import Oberwolfach.MarkedOrdinarySpokeChangeGraph
public import Oberwolfach.HubSelectedClassGeometry

@[expose] public section
/-! An upper bound on loss and a bound on the change of size control both
directions of the ordinary spoke change. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem changed_card_from_loss_and_size {X:Type} [DecidableEq X] (A B:Finset X):
    ((changed A B).card:ℝ)=2*((A\B).card:ℝ)+(B.card:ℝ)-(A.card:ℝ):=by
  have ha:=Finset.card_sdiff_add_card_inter A B
  have hb:=Finset.card_sdiff_add_card_inter B A
  have ha':((A\B).card:ℝ)+(A∩B).card=A.card:=by exact_mod_cast ha
  have hb':((B\A).card:ℝ)+(A∩B).card=B.card:=by
    rw [Finset.inter_comm]
    exact_mod_cast hb
  rw [changed_card_eq_differences]
  push_cast
  linarith

variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem marked_spoke_change_from_loss_and_size
    (H H':Bool→V→U→Prop) (hmark:∀x u,H true x u↔H' true x u)
    (lossRow sizeRow lossCol sizeCol:ℝ)
    (hLossRow:∀x,((Finset.univ.filter (fun u=>H false x u∧¬H' false x u)).card:ℝ)≤lossRow)
    (hSizeRow:∀x,((Finset.univ.filter (fun u=>H' false x u)).card:ℝ)-
      ((Finset.univ.filter (fun u=>H false x u)).card:ℝ)≤sizeRow)
    (hLossCol:∀u,((Finset.univ.filter (fun x=>H false x u∧¬H' false x u)).card:ℝ)≤lossCol)
    (hSizeCol:∀u,((Finset.univ.filter (fun x=>H' false x u)).card:ℝ)-
      ((Finset.univ.filter (fun x=>H false x u)).card:ℝ)≤sizeCol):
    (∀x:V,((markedSpokeChangeGraph H H').degree (Sum.inl x):ℝ)≤2*lossRow+sizeRow) ∧
    (∀u:U,((markedSpokeChangeGraph H H').degree (Sum.inr u):ℝ)≤2*lossCol+sizeCol):=by
  have helper:∀{X:Type} [Fintype X] [DecidableEq X] (A B:X→Prop),
      ((Finset.univ.filter (fun x=>¬(A x↔B x))).card:ℝ)=
        2*((Finset.univ.filter (fun x=>A x∧¬B x)).card:ℝ)+
        ((Finset.univ.filter B).card:ℝ)-((Finset.univ.filter A).card:ℝ):=by
    intro X _ _ A B
    let As:=Finset.univ.filter A
    let Bs:=Finset.univ.filter B
    have hc:Finset.univ.filter (fun x=>¬(A x↔B x))=changed As Bs:=by
      ext x
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,changed,Finset.mem_union,Finset.mem_sdiff,As,Bs]
      tauto
    have hl:Finset.univ.filter (fun x=>A x∧¬B x)=As\Bs:=by
      ext x
      simp [As,Bs]
    rw [hc,hl]
    exact changed_card_from_loss_and_size As Bs
  obtain ⟨hl,hr⟩:=marked_spoke_change_graph_ordinary_only H H' hmark
  constructor
  · intro x
    rw [hl,helper]
    linarith [hLossRow x,hSizeRow x]
  · intro u
    rw [hr,helper]
    linarith [hLossCol u,hSizeCol u]
end Oberwolfach
