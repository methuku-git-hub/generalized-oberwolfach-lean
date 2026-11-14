module

public import Oberwolfach.OrdinaryOuterHostBalance
public import Oberwolfach.OrdinaryDeletedHostBalance

@[expose] public section
/-! After protecting the inner pair, a further reserved boundary subgraph
costs only its actual row degrees in the approximate-packing balance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_reserve_outer_balance
    (Q D:SimpleGraph V) (H S:V→U→Prop) (I:Finset V) (J:Finset U) (dr ds:ℝ)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hD:D≤Q\spanningRestriction Q I)
    (hS:∀v u,S v u→H v u∧¬(v∈I∧u∈J))
    (hDdeg:∀v,(D.degree v:ℝ)≤dr)
    (hSdeg:∀v,((Finset.univ.filter (S v)).card:ℝ)≤ds):
    ∀v,|(((Q\spanningRestriction Q I)\D).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧¬(v∈I∧u∈J)∧¬S v u)).card|≤
        (I.card:ℝ)+2*J.card+dr+2*ds:=by
  have hbase:∀v,|(((Q\spanningRestriction Q I).degree v):ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧¬(v∈I∧u∈J))).card|≤(I.card:ℝ)+2*J.card:=by
    intro v
    convert ordinary_outer_host_balance Q H I J hbal v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have h:=ordinary_deleted_host_balance (Q\spanningRestriction Q I) D
    (fun v u=>H v u∧¬(v∈I∧u∈J)) S ((I.card:ℝ)+2*J.card) dr ds hD hS
    (by intro v;convert hbase v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hDdeg hSdeg
  intro v
  have he:(Finset.univ.filter (fun u=>H v u∧¬(v∈I∧u∈J)∧¬S v u))=
      Finset.univ.filter (fun u=>(H v u∧¬(v∈I∧u∈J))∧¬S v u):=by
    ext u;simp only [Finset.mem_filter,Finset.mem_univ,true_and];tauto
  rw [he]
  convert h v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
