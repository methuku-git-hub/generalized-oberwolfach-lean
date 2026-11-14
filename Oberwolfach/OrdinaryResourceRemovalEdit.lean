module

public import Oberwolfach.OrdinaryResourceSubgraphs
public import Oberwolfach.OrdinaryTransformerForbiddenEdges
public import Oberwolfach.OrdinaryProtectedBoundaryEdit
public import Oberwolfach.HubToRowDeletion

@[expose] public section
/-! Removing a resource reservoir changes any physical neighbourhood by at
most the number of rows and hubs it occupies. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_resource_physical_degree_bound (Q:SimpleGraph V) (H:V→U→Prop)
    (K:Finset (Sym2 V⊕(V×U))) (hK:K⊆ordinaryHostResources Q H):
    ∀w:V⊕U,(ordinaryPhysicalGraph (ordinaryResourceRim Q K) (fun v u=>Sum.inr (v,u)∈K)).degree w≤
      (ordinaryResourceRows K).card+(ordinaryResourceHubs K).card:=by
  let D:=ordinaryPhysicalGraph (ordinaryResourceRim Q K) (fun v u=>Sum.inr (v,u)∈K)
  have horder:D.support.toFinset.card≤(ordinaryResourceRows K).card+(ordinaryResourceHubs K).card:=by
    apply ordinary_resource_subgraph_order Q H K hK
    · intro v w he
      exact ⟨Finset.mem_biUnion.mpr ⟨Sum.inl s(v,w),he,by simp⟩,
        Finset.mem_biUnion.mpr ⟨Sum.inl s(v,w),he,by simp⟩⟩
    · intro v u he
      exact ⟨Finset.mem_biUnion.mpr ⟨Sum.inr (v,u),he,by simp⟩,
        Finset.mem_biUnion.mpr ⟨Sum.inr (v,u),he,by simp⟩⟩
  intro w
  have hn:D.neighborFinset w⊆D.support.toFinset:=by
    intro v hv
    have ha:D.Adj w v:=by simpa only [SimpleGraph.mem_neighborFinset] using hv
    exact Set.mem_toFinset.mpr ⟨w,ha.symm⟩
  have hc:=Finset.card_le_card hn
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hc
  exact hc.trans horder

theorem ordinary_resource_removal_physical_edit (Q:SimpleGraph V) (H:V→U→Prop)
    (K:Finset (Sym2 V⊕(V×U))) (hK:K⊆ordinaryHostResources Q H):
    ∀w:V⊕U,((changed ((ordinaryPhysicalGraph Q H).neighborFinset w)
      ((ordinaryPhysicalGraph (Q\ordinaryResourceRim Q K) (fun v u=>H v u∧¬(Sum.inr (v,u)∈K))).neighborFinset w)).card:ℝ)≤
      (ordinaryResourceRows K).card+(ordinaryResourceHubs K).card:=by
  let D:=ordinaryPhysicalGraph (ordinaryResourceRim Q K) (fun v u=>Sum.inr (v,u)∈K)
  have he:ordinaryPhysicalGraph (Q\ordinaryResourceRim Q K) (fun v u=>H v u∧¬(Sum.inr (v,u)∈K))=
      ordinaryPhysicalGraph Q H\D:=by
    exact ordinary_physical_graph_after_deletion Q H D
  intro w
  have hh:=graph_changed_neighbors_after_deletion (ordinaryPhysicalGraph Q H) D w
  have hb:=ordinary_resource_physical_degree_bound Q H K hK w
  have hc:((changed ((ordinaryPhysicalGraph Q H).neighborFinset w) ((ordinaryPhysicalGraph Q H\D).neighborFinset w)).card:ℝ)≤
      (ordinaryResourceRows K).card+(ordinaryResourceHubs K).card:=by
    exact_mod_cast hh.trans hb
  rw [he]
  convert hc using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _

theorem ordinary_resource_removal_from_reference (R Q:SimpleGraph V) (J H:V→U→Prop)
    (K:Finset (Sym2 V⊕(V×U))) (hK:K⊆ordinaryHostResources Q H) (L:ℝ)
    (hedit:∀w:V⊕U,((changed ((ordinaryPhysicalGraph R J).neighborFinset w)
      ((ordinaryPhysicalGraph Q H).neighborFinset w)).card:ℝ)≤L):
    ∀w:V⊕U,((changed ((ordinaryPhysicalGraph R J).neighborFinset w)
      ((ordinaryPhysicalGraph (Q\ordinaryResourceRim Q K) (fun v u=>H v u∧¬(Sum.inr (v,u)∈K))).neighborFinset w)).card:ℝ)≤
      L+((ordinaryResourceRows K).card:ℝ)+(ordinaryResourceHubs K).card:=by
  intro w
  have ht:((changed ((ordinaryPhysicalGraph R J).neighborFinset w)
      ((ordinaryPhysicalGraph (Q\ordinaryResourceRim Q K) (fun v u=>H v u∧¬(Sum.inr (v,u)∈K))).neighborFinset w)).card:ℝ)≤
      ((changed ((ordinaryPhysicalGraph R J).neighborFinset w) ((ordinaryPhysicalGraph Q H).neighborFinset w)).card:ℝ)+
      ((changed ((ordinaryPhysicalGraph Q H).neighborFinset w)
        ((ordinaryPhysicalGraph (Q\ordinaryResourceRim Q K) (fun v u=>H v u∧¬(Sum.inr (v,u)∈K))).neighborFinset w)).card:ℝ):=by
    exact_mod_cast changed_card_triangle ((ordinaryPhysicalGraph R J).neighborFinset w)
      ((ordinaryPhysicalGraph Q H).neighborFinset w)
      ((ordinaryPhysicalGraph (Q\ordinaryResourceRim Q K) (fun v u=>H v u∧¬(Sum.inr (v,u)∈K))).neighborFinset w)
  have hr:=ordinary_resource_removal_physical_edit Q H K hK w
  linarith only [ht,hedit w,hr]
end Oberwolfach
