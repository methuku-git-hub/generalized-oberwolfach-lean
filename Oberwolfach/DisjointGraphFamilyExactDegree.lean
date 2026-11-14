module

public import Oberwolfach.GraphDeletion

@[expose] public section
/-! Edge-disjoint graph families have additive degrees in their union. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem disjoint_graph_family_exact_degree {V U:Type} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U] (G:U→SimpleGraph V)
    (hdis:∀u v,u≠v→Disjoint (G u).edgeFinset (G v).edgeFinset) (x:V):
    (⨆u,G u).degree x=∑u,(G u).degree x :=by
  have hneigh:(⨆u,G u).neighborFinset x=Finset.univ.biUnion (fun u=>(G u).neighborFinset x):=by
    ext y
    simp only [SimpleGraph.mem_neighborFinset,SimpleGraph.iSup_adj,Finset.mem_biUnion,Finset.mem_univ,true_and]
  have hp:(↑(Finset.univ:Finset U):Set U).PairwiseDisjoint (fun u=>(G u).neighborFinset x):=by
    intro u hu v hv huv
    apply Finset.disjoint_left.mpr
    intro y hyu hyv
    have heu:s(x,y)∈(G u).edgeFinset:=by simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,SimpleGraph.mem_neighborFinset] using hyu
    have hev:s(x,y)∈(G v).edgeFinset:=by simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,SimpleGraph.mem_neighborFinset] using hyv
    exact Finset.disjoint_left.mp (hdis u v huv) heu hev
  rw [←SimpleGraph.card_neighborFinset_eq_degree,hneigh,Finset.card_biUnion hp]
  simp only [SimpleGraph.card_neighborFinset_eq_degree]
end Oberwolfach
