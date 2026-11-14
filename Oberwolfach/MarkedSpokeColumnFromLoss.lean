module

public import Oberwolfach.MarkedSpokeChangesFromLoss

@[expose] public section
/-! For fixed-hub fields only the local losses and local size discrepancy
are needed; no vertex-side change bound is required. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_spoke_column_from_loss_and_size
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (H H':Bool→V→U→Prop) (hmark:∀x u,H true x u↔H' true x u)
    (lossCol sizeCol:ℝ)
    (hLossCol:∀u,((Finset.univ.filter (fun x=>H false x u∧¬H' false x u)).card:ℝ)≤lossCol)
    (hSizeCol:∀u,((Finset.univ.filter (fun x=>H' false x u)).card:ℝ)-
      ((Finset.univ.filter (fun x=>H false x u)).card:ℝ)≤sizeCol):
    ∀u:U,((markedSpokeChangeGraph H H').degree (Sum.inr u):ℝ)≤2*lossCol+sizeCol :=by
  have hLossRow:∀x,((Finset.univ.filter (fun u=>H false x u∧¬H' false x u)).card:ℝ)≤Fintype.card U:=by
    intro x
    exact_mod_cast Finset.card_le_univ _
  have hSizeRow:∀x,((Finset.univ.filter (fun u=>H' false x u)).card:ℝ)-
      ((Finset.univ.filter (fun u=>H false x u)).card:ℝ)≤Fintype.card U:=by
    intro x
    have h:( (Finset.univ.filter (fun u=>H' false x u)).card:ℝ)≤Fintype.card U:=by exact_mod_cast Finset.card_le_univ _
    have h0:(0:ℝ)≤(Finset.univ.filter (fun u=>H false x u)).card:=by positivity
    linarith
  exact (marked_spoke_change_from_loss_and_size H H' hmark (Fintype.card U) (Fintype.card U) lossCol sizeCol hLossRow hSizeRow hLossCol hSizeCol).2
end Oberwolfach
