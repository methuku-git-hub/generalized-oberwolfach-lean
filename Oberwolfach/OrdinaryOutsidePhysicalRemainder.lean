module

public import Oberwolfach.OrdinaryPhysicalResourceIncidence
public import Oberwolfach.OrdinaryBoundaryGraph

@[expose] public section
/-! Outside-outside edges of the actual host lie in the unreserved graph
left by the approximate packing, so its sparse degree controls cleanup. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_physical_outside_restriction (Q:SimpleGraph V) (H:V→U→Prop)
    (X:Finset V) (Z:Finset U):
    ordinaryPhysicalGraph (spanningRestriction Q (Finset.univ\X))
      (fun v u=>H v u∧v∉X∧u∉Z)=
      spanningRestriction (ordinaryPhysicalGraph Q H) (Finset.univ\ordinaryInnerVertices X Z):=by
  ext a b
  rw [spanningRestriction_adj]
  cases a with
  | inl v=>
    cases b with
    | inl w=>simp [ordinaryPhysicalGraph,spanningRestriction_adj,ordinaryInnerVertices_left]
    | inr u=>simp [ordinaryPhysicalGraph,ordinaryInnerVertices_left,ordinaryInnerVertices_right]
  | inr u=>
    cases b with
    | inl v=>simp [ordinaryPhysicalGraph,ordinaryInnerVertices_left,ordinaryInnerVertices_right] <;> tauto
    | inr u'=>simp [ordinaryPhysicalGraph]

theorem ordinary_outside_physical_edges_in_unreserved_remainder
    (Q₀ Q:SimpleGraph V) (H₀ H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (C:SimpleGraph (V⊕U)) (σ:Sym2 (V⊕U)→Bool)
    (hpost:ordinaryPhysicalGraph Q H≤ordinaryPhysicalGraph Q₀ H₀\C):
    ordinaryPhysicalGraph (spanningRestriction Q (Finset.univ\X))
      (fun v u=>H v u∧v∉X∧u∉Z)≤
      ((ordinaryPhysicalGraph Q₀ H₀\spanningRestriction (ordinaryPhysicalGraph Q₀ H₀) (ordinaryInnerVertices X Z))\
        retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ)\C:=by
  rw [ordinary_physical_outside_restriction]
  intro a b hab
  have ho:=(spanningRestriction_adj (ordinaryPhysicalGraph Q H) (Finset.univ\ordinaryInnerVertices X Z) a b).mp hab
  have ha:a∉ordinaryInnerVertices X Z:=(Finset.mem_sdiff.mp ho.2.1).2
  have hb:b∉ordinaryInnerVertices X Z:=(Finset.mem_sdiff.mp ho.2.2).2
  have hp:=hpost ho.1
  refine ⟨⟨⟨hp.1,?_⟩,?_⟩,hp.2⟩
  · intro h
    exact ha ((spanningRestriction_adj _ _ _ _).mp h).2.1
  · intro h
    have hh:=(ordinaryBoundaryGraph_adj Q₀ H₀ X Z a b).mp h.1
    rcases hh.2 with ⟨_,hbin⟩|⟨_,hain⟩
    · exact hb hbin
    · exact ha hain

theorem ordinary_outside_resources_bounded_by_unreserved_remainder
    (Q₀ Q:SimpleGraph V) (H₀ H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (C:SimpleGraph (V⊕U)) (σ:Sym2 (V⊕U)→Bool) (D:ℕ)
    (hpost:ordinaryPhysicalGraph Q H≤ordinaryPhysicalGraph Q₀ H₀\C)
    (hdegree:∀w,((((ordinaryPhysicalGraph Q₀ H₀\spanningRestriction (ordinaryPhysicalGraph Q₀ H₀)
      (ordinaryInnerVertices X Z))\retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ)\C).degree w)≤D):
    let E:=ordinaryHostResources (spanningRestriction Q (Finset.univ\X)) (fun v u=>H v u∧v∉X∧u∉Z);
    (∀w,(E.filter (ordinaryResourceIncident w)).card≤D) ∧ E.card≤Fintype.card (V⊕U)*D:=by
  intro E
  have hsub:=ordinary_outside_physical_edges_in_unreserved_remainder Q₀ Q H₀ H X Z C σ hpost
  have hd:∀w,(ordinaryPhysicalGraph (spanningRestriction Q (Finset.univ\X))
      (fun v u=>H v u∧v∉X∧u∉Z)).degree w≤D:=by
    intro w
    exact (SimpleGraph.degree_le_of_le hsub (v:=w)).trans (hdegree w)
  exact ordinary_resources_from_physical_degree _ _ E D (fun _ h=>h) hd
end Oberwolfach
