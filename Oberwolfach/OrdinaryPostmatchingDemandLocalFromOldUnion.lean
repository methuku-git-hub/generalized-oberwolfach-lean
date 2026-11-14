module

public import Oberwolfach.OrdinaryPostmatchingDemandFromOldUnion
public import Oberwolfach.OrdinaryPostmatchingRequiredLocalDegree

@[expose] public section
/-! The post-matching demand needs uncovered sample edges only on the
protected vertex set. All conclusions concern the same chosen old edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_postmatching_demand_local_from_old_union
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (Old:U→Finset (Sym2 V)) (Host Target Sample Reference Protect Bad:SimpleGraph V) (Inner:Finset V)
    (edit localLoss forbidden:ℝ) (hOldHost:∀u,Old u⊆Host.edgeFinset)
    (hOldRef:∀u,Disjoint (Old u) Reference.edgeFinset)
    (hRef:Reference≤Sample) (hProtect:Protect≤Reference) (hDis:Disjoint Reference Bad)
    (hEdit:∀v,((Finset.univ.filter (fun w=>Xor (Target.Adj v w) (Sample.Adj v w))).card:ℝ)≤edit)
    (hLocal:∀v,((spanningRestriction ((Sample\Reference)\prescribedPhysicalUnion Old) Inner).degree v:ℝ)≤localLoss)
    (hBad:∀v,(Bad.degree v:ℝ)≤forbidden):
    let Used:=prescribedPhysicalUnion Old
    let G:=ordinaryPostmatchingRequired Target Sample Reference Bad Used Inner;
    G≤Target\Protect ∧ Disjoint G Used ∧ Disjoint Used Reference ∧
    (∀u,Disjoint (Old u) G.edgeFinset) ∧
    (∀v,(G.degree v:ℝ)≤edit+localLoss+forbidden) ∧
    ordinaryForbiddenRequired Target Sample Reference Bad Inner≤Used⊔G :=by
  intro Used G
  have h:=ordinary_postmatching_required_relations Target Sample Reference Protect Bad Used Inner hRef hProtect hDis
  refine ⟨h.1,h.2.1,ordinary_old_union_avoids_reference Old Reference hOldRef,?_,?_,h.2.2.1⟩
  · exact ordinary_old_union_postmatching_avoidance Old Host Target Sample Reference Bad Inner hOldHost
  · exact ordinary_postmatching_required_local_degree Target Sample Reference Bad Used Inner edit localLoss forbidden hEdit hLocal hBad
end Oberwolfach
