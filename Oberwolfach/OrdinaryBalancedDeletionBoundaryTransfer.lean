module

public import Oberwolfach.OrdinaryInnerBalanceFromBalancedDeletionBoundary

@[expose] public section
/-! Transfer induced near balance through a globally balanced deletion using
its boundary discrepancy rather than its total degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_balanced_deletion_boundary_transfer
    (Q R:SimpleGraph V) (H E:V→U→Prop) (I:Finset V) (J:Finset U) (b c d:ℝ)
    (hRQ:R≤Q) (hEH:∀v u,E v u→H v u)
    (hparent:∀v,|((spanningRestriction Q I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧v∈I∧u∈J)).card|≤b)
    (hfull:∀v,|(R.degree v:ℝ)-2*(Finset.univ.filter (E v)).card|≤c)
    (hboundary:∀v,|((R\spanningRestriction R I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>E v u∧¬(v∈I∧u∈J))).card|≤d):
    ∀v,|((spanningRestriction (Q\R) I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧¬E v u∧v∈I∧u∈J)).card|≤b+(c+d) :=by
  let QI:=spanningRestriction Q I
  let RI:=spanningRestriction R I
  let HI:=fun v u=>H v u∧v∈I∧u∈J
  let EI:=fun v u=>E v u∧v∈I∧u∈J
  have hRI:RI≤QI:=by
    intro x y h
    obtain ⟨hR,hx,hy⟩:=(spanningRestriction_adj R I x y).mp h
    exact (spanningRestriction_adj Q I x y).mpr ⟨hRQ hR,hx,hy⟩
  have hEI:∀v u,EI v u→HI v u:=by intro v u h;exact ⟨hEH v u h.1,h.2⟩
  have hdel:∀v,|(RI.degree v:ℝ)-2*(Finset.univ.filter (EI v)).card|≤c+d:=
    ordinary_inner_balance_from_balanced_deletion_boundary R E I J c d hfull hboundary
  have hh:=ordinary_deleted_host_balance_refined QI RI HI EI b (c+d) hRI hEI
    (by intro v;convert hparent v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro v;convert hdel v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  have hgraph:QI\RI=spanningRestriction (Q\R) I:=by
    ext x y
    simp only [QI,RI,SimpleGraph.sdiff_adj,spanningRestriction_adj]
    tauto
  intro v
  have hrow:(Finset.univ.filter (fun u=>HI v u∧¬EI v u))=
      Finset.univ.filter (fun u=>H v u∧¬E v u∧v∈I∧u∈J):=by
    ext u
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,HI,EI]
    tauto
  have hv:=hh v
  have hd:((QI\RI).degree v:ℝ)=((spanningRestriction (Q\R) I).degree v:ℝ):=by
    have ht:=congrArg (fun G:SimpleGraph V=>(G.degree v:ℝ)) hgraph
    convert ht using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hv':|((QI\RI).degree v:ℝ)-2*(Finset.univ.filter (fun u=>HI v u∧¬EI v u)).card|≤b+(c+d):=by
    convert hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  rw [hd,hrow] at hv'
  exact hv' 
end Oberwolfach
