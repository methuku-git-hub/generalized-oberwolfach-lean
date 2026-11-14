module

public import Oberwolfach.OrdinaryOuterHostBalanceRefined
public import Oberwolfach.OrdinaryDeletedHostBalanceRefinedAt

@[expose] public section
/-! A globally balanced deletion has small induced imbalance whenever its
cross-boundary portion is balanced. This charges boundary imbalance, not the
number of deleted edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_inner_balance_from_balanced_deletion_boundary_at
    (R:SimpleGraph V) (E:V→U→Prop) (I:Finset V) (J:Finset U) (b c:ℝ) (v:V)
    (hfull:|(R.degree v:ℝ)-2*(Finset.univ.filter (E v)).card|≤b)
    (hboundary:|((R\spanningRestriction R I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>E v u∧¬(v∈I∧u∈J))).card|≤c):
    |((spanningRestriction R I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>E v u∧v∈I∧u∈J)).card|≤b+c :=by
  let Rb:=R\spanningRestriction R I
  let Eb:=fun v u=>E v u∧¬(v∈I∧u∈J)
  have hsub:Rb≤R:=by intro x y h;exact h.1
  have hspoke:∀v u,Eb v u→E v u:=by intro v u h;exact h.1
  have hbound:|(Rb.degree v:ℝ)-2*(Finset.univ.filter (Eb v)).card|≤c:=hboundary
  have hresult:=ordinary_deleted_host_balance_refined_at R Rb E Eb b c hsub hspoke v hfull
    (by convert hbound using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  have hgraph:R\Rb=spanningRestriction R I:=by
    ext x y
    simp only [Rb,SimpleGraph.sdiff_adj,spanningRestriction_adj]
    tauto
  have hrow:(Finset.univ.filter (fun u=>E v u∧¬Eb v u))=
      Finset.univ.filter (fun u=>E v u∧v∈I∧u∈J):=by
    ext u
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Eb]
    tauto
  have hh:=hresult
  have hd:((R\Rb).degree v:ℝ)=((spanningRestriction R I).degree v:ℝ):=by
    have ht:=congrArg (fun G:SimpleGraph V=>(G.degree v:ℝ)) hgraph
    convert ht using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hh':|((R\Rb).degree v:ℝ)-2*(Finset.univ.filter (fun u=>E v u∧¬Eb v u)).card|≤b+c:=by
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  rw [hd,hrow] at hh'
  exact hh'
end Oberwolfach
