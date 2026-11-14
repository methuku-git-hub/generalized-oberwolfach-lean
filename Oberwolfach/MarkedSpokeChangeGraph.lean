module

public import Oberwolfach.MarkedFinitePhysicalDeletion

@[expose] public section
/-! Build the physical change graph directly from typed spoke disagreements. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

def markedSpokeChangeGraph (H H':Bool→V→U→Prop):SimpleGraph (V⊕U):=
  markedFiniteSpokeGraph (Finset.univ.filter (fun z:V×U=>∃b,¬(H b z.1 z.2↔H' b z.1 z.2)))

theorem marked_spoke_change_graph_adj (H H':Bool→V→U→Prop) (x:V) (u:U):
    (markedSpokeChangeGraph H H').Adj (Sum.inl x) (Sum.inr u)↔∃b,¬(H b x u↔H' b x u):=by
  simp only [markedSpokeChangeGraph,markedFiniteSpokeGraph_adj,Finset.mem_filter,Finset.mem_univ,true_and]

theorem marked_spoke_change_graph_degrees (H H':Bool→V→U→Prop):
    (∀x:V,(markedSpokeChangeGraph H H').degree (Sum.inl x)=
      (Finset.univ.filter (fun u=>∃b,¬(H b x u↔H' b x u))).card) ∧
    (∀u:U,(markedSpokeChangeGraph H H').degree (Sum.inr u)=
      (Finset.univ.filter (fun x=>∃b,¬(H b x u↔H' b x u))).card):=by
  let FS:=markedSpokeChangeGraph H H'
  have hleft:∀x y:V,¬FS.Adj (Sum.inl x) (Sum.inl y):=by
    intro x y h
    obtain ⟨z,hz,he⟩:=Finset.mem_image.mp h.2
    have hh:Sum.inr z.2∈({Sum.inl x,Sum.inl y}:Finset (V⊕U)):=he ▸ (by simp)
    simp only [Finset.mem_insert,Finset.mem_singleton,Sum.inr_ne_inl,or_self] at hh
  have hright:∀u v:U,¬FS.Adj (Sum.inr u) (Sum.inr v):=by
    intro u v h
    obtain ⟨z,hz,he⟩:=Finset.mem_image.mp h.2
    have hh:Sum.inl z.1∈({Sum.inr u,Sum.inr v}:Finset (V⊕U)):=he ▸ (by simp)
    simp only [Finset.mem_insert,Finset.mem_singleton,Sum.inl_ne_inr,or_self] at hh
  constructor
  · intro x
    let A:=Finset.univ.filter (fun u=>∃b,¬(H b x u↔H' b x u))
    have heq:FS.neighborFinset (Sum.inl x)=A.image Sum.inr:=by
      ext z
      cases z with
      | inl y => simp [SimpleGraph.mem_neighborFinset,Finset.mem_image,hleft x y]
      | inr u => simpa [SimpleGraph.mem_neighborFinset,A] using marked_spoke_change_graph_adj H H' x u
    rw [←SimpleGraph.card_neighborFinset_eq_degree,heq,Finset.card_image_of_injective _ Sum.inr_injective]
  · intro u
    let A:=Finset.univ.filter (fun x=>∃b,¬(H b x u↔H' b x u))
    have heq:FS.neighborFinset (Sum.inr u)=A.image Sum.inl:=by
      ext z
      cases z with
      | inl x => simpa [SimpleGraph.mem_neighborFinset,A] using (FS.adj_comm _ _).trans (marked_spoke_change_graph_adj H H' x u)
      | inr v => simp [SimpleGraph.mem_neighborFinset,Finset.mem_image,hright u v]
    rw [←SimpleGraph.card_neighborFinset_eq_degree,heq,Finset.card_image_of_injective _ Sum.inl_injective]
end Oberwolfach
