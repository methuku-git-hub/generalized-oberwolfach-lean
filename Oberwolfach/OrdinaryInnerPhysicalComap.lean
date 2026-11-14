module

public import Oberwolfach.OrdinaryProtectedTraceInnerEdit
public import Oberwolfach.OrdinaryPhysicalEditToTypedChanges

@[expose] public section
/-! Pull physical edit bounds to the two induced vertex types of a level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A B:Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem graph_changed_comap_le (G H:SimpleGraph B) (e:A↪B) (a:A):
    (changed ((G.comap e).neighborFinset a) ((H.comap e).neighborFinset a)).card≤
      (changed (G.neighborFinset (e a)) (H.neighborFinset (e a))).card:=by
  have hs:(changed ((G.comap e).neighborFinset a) ((H.comap e).neighborFinset a)).image e ⊆
      changed (G.neighborFinset (e a)) (H.neighborFinset (e a)):=by
    intro b hb
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hb
    simpa only [changed,Finset.mem_union,Finset.mem_sdiff,SimpleGraph.mem_neighborFinset,SimpleGraph.comap_adj] using hx
  have hh:=Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ e.injective] at hh
  exact hh

variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryInnerEmbedding (X:Finset V) (Z:Finset U):↥X⊕↥Z↪V⊕U:=
  (⟨Subtype.val,Subtype.val_injective⟩:↥X↪V).sumMap (⟨Subtype.val,Subtype.val_injective⟩:↥Z↪U)

theorem ordinary_inner_embedding_mem (X:Finset V) (Z:Finset U) (a:↥X⊕↥Z):
    ordinaryInnerEmbedding X Z a∈ordinaryInnerVertices X Z:=by
  cases a with
  | inl v=>exact (ordinaryInnerVertices_left X Z v.val).mpr v.property
  | inr u=>exact (ordinaryInnerVertices_right X Z u.val).mpr u.property

theorem ordinary_inner_comap_spanning (K:SimpleGraph (V⊕U)) (X:Finset V) (Z:Finset U):
    (spanningRestriction K (ordinaryInnerVertices X Z)).comap (ordinaryInnerEmbedding X Z)=
      K.comap (ordinaryInnerEmbedding X Z):=by
  ext a b
  simp only [SimpleGraph.comap_adj,spanningRestriction_adj]
  exact ⟨fun h=>h.1,fun h=>⟨h,ordinary_inner_embedding_mem X Z a,ordinary_inner_embedding_mem X Z b⟩⟩

theorem ordinary_induced_physical_comap (Q:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U):
    ordinaryPhysicalGraph (Q.induce (X:Set V)) (fun (v:↥X) (u:↥Z)=>H v.val u.val)=
      (ordinaryPhysicalGraph Q H).comap (ordinaryInnerEmbedding X Z):=by
  ext a b
  cases a <;> cases b <;> rfl
end Oberwolfach
