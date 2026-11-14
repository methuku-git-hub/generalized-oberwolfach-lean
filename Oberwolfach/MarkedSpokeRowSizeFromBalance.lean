module

public import Oberwolfach.MarkedSpokeColumnSizeFromBalance

@[expose] public section
/-! Exact corrected row balance, reference balance, and a directed-rim count
bound control the ordinary-spoke row size. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem marked_spoke_row_size_from_balance
    (H H':Bool→V→U→Prop) (oldRim newRim:V→ℝ) (ε δ:ℝ)
    (hmark:∀x u,H true x u↔H' true x u)
    (hOld:∀x,|oldRim x-
      (((Finset.univ.filter (fun u=>H false x u)).card:ℝ)+
       ((Finset.univ.filter (fun u=>H true x u)).card:ℝ))|≤ε)
    (hNew:∀x,newRim x=
      ((Finset.univ.filter (fun u=>H' false x u)).card:ℝ)+
      ((Finset.univ.filter (fun u=>H' true x u)).card:ℝ))
    (hRim:∀x,newRim x-oldRim x≤δ):
    ∀x,((Finset.univ.filter (fun u=>H' false x u)).card:ℝ)-
      ((Finset.univ.filter (fun u=>H false x u)).card:ℝ)≤ε+δ:=by
  intro x
  have he:(Finset.univ.filter (fun u=>H true x u))=
      Finset.univ.filter (fun u=>H' true x u):=by
    ext u
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,hmark]
  have hh:=(abs_le.mp (hOld x)).2
  have hn:=hNew x
  rw [←he] at hn
  linarith [hn,hRim x]
end Oberwolfach
