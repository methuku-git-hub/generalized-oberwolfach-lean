module

public import Oberwolfach.MarkedSpokeChangesFromLoss

@[expose] public section
/-! Exact corrected column balance and approximate reference balance bound
the ordinary-spoke column size change. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem marked_spoke_column_size_from_balance
    (H H':Bool→V→U→Prop) (m:ℕ) (ε:ℝ)
    (hmark:∀x u,H true x u↔H' true x u)
    (hOld:∀u,|((Finset.univ.filter (fun x=>H false x u)).card:ℝ)-
      (m:ℝ)*(Finset.univ.filter (fun x=>H true x u)).card|≤ε)
    (hNew:∀u,(Finset.univ.filter (fun x=>H' false x u)).card=
      m*(Finset.univ.filter (fun x=>H' true x u)).card):
    ∀u,((Finset.univ.filter (fun x=>H' false x u)).card:ℝ)-
      ((Finset.univ.filter (fun x=>H false x u)).card:ℝ)≤ε:=by
  intro u
  have he:(Finset.univ.filter (fun x=>H true x u))=
      Finset.univ.filter (fun x=>H' true x u):=by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,hmark]
  have hn:((Finset.univ.filter (fun x=>H' false x u)).card:ℝ)=
      (m:ℝ)*(Finset.univ.filter (fun x=>H true x u)).card:=by
    rw [he]
    exact_mod_cast hNew u
  have hh:=(abs_le.mp (hOld u)).1
  linarith
end Oberwolfach
