module

public import Oberwolfach.OrdinaryAttachmentRimInjection
public import Oberwolfach.OrdinaryAttachmentSpokeInjection
public import Oberwolfach.OrdinaryAttachmentPreimages
public import Oberwolfach.OrdinaryDecompositionEdges
public import Oberwolfach.CanonicalEdgeDarts

@[expose] public section

/-! The finite expansion-to-attachment map is a bijection on physical
resources. The final theorem discharges the encoding hypotheses for the
actual edges and spokes of a given graph pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E J W : Type}
variable [Fintype V] [Fintype U] [Fintype E] [Fintype J] [Fintype W]
variable [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq J] [DecidableEq W]

def attachmentResourceMap (z : W) (ρ : E⊕J → V) :
    (Sym2 (ExpansionRow V E J W) ⊕ (ExpansionRow V E J W × ExpansionHub U E J)) →
    (Sym2 (ExpansionRow V E J W) ⊕ (ExpansionRow V E J W × ExpansionHub U E J)) :=
  Sum.map (Sym2.map (attachmentCollapse z ρ)) (Prod.map (attachmentCollapse z ρ) id)

theorem ordinaryExpansion_attachment_resources_image
    (G : SimpleGraph V) (H : V → U → Prop) (C : SimpleGraph W) (z o : W) (hzo : C.Adj z o)
    (x y : E → V) (v : J → V) (u : J → U)
    (hG : ∀ e,G.Adj (x e) (y e)) (hH : ∀ j,H (v j) (u j))
    (hGc : ∀ a b,G.Adj a b → ∃ e,s(x e,y e)=s(a,b))
    (hHc : ∀ a b,H a b → ∃ j,v j=a ∧ u j=b) :
    (ordinaryHostResources (ordinaryExpansionRim C z o x y) (ordinaryExpansionSpokes z v u)).image
      (attachmentResourceMap z (expansionAttachmentRoots x v))=
    ordinaryHostResources (ordinaryAttachmentRim G C z (expansionAttachmentRoots x v))
      (ordinaryAttachmentSpokes H z (expansionAttachmentRoots x v)) := by
  ext e
  constructor
  · intro himage
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp himage
    cases e with
    | inl e =>
      rw [ordinaryHostResources_rim] at he
      induction e using Sym2.ind with
      | _ a b =>
        exact (ordinaryHostResources_rim _ _ _).mpr
          (ordinaryExpansion_attachment_rim_hom G C z o hzo x y v hG a b he)
    | inr p =>
      rcases p with ⟨a,b⟩
      rw [ordinaryHostResources_spoke] at he
      exact (ordinaryHostResources_spoke _ _ _ _).mpr
        (ordinaryExpansion_attachment_spoke_hom H z x v u hH a b he)
  · intro he
    cases e with
    | inl e =>
      rw [ordinaryHostResources_rim] at he
      induction e using Sym2.ind with
      | _ a b =>
        obtain ⟨a',b',hab,ha,hb⟩ := ordinaryExpansion_attachment_rim_preimage G C z o x y v hGc a b he
        refine Finset.mem_image.mpr ⟨.inl s(a',b'),(ordinaryHostResources_rim _ _ _).mpr hab,?_⟩
        change Sum.inl s(attachmentCollapse z (expansionAttachmentRoots x v) a',
          attachmentCollapse z (expansionAttachmentRoots x v) b')=Sum.inl s(a,b)
        rw [ha,hb]
    | inr p =>
      rcases p with ⟨a,b⟩
      rw [ordinaryHostResources_spoke] at he
      obtain ⟨a',hab,ha⟩ := ordinaryExpansion_attachment_spoke_preimage H z x v u hHc a b he
      refine Finset.mem_image.mpr ⟨.inr (a',b),(ordinaryHostResources_spoke _ _ _ _).mpr hab,?_⟩
      change Sum.inr (attachmentCollapse z (expansionAttachmentRoots x v) a',b)=Sum.inr (a,b)
      rw [ha]

theorem ordinaryExpansion_attachment_resources_injective
    (C : SimpleGraph W) (z o : W) (hzo : z≠o) (x y : E → V) (v : J → V) (u : J → U)
    (hxy : Function.Injective (fun e => s(x e,y e))) (hvu : Function.Injective (fun j => (v j,u j))) :
    Set.InjOn (attachmentResourceMap (U:=U) z (expansionAttachmentRoots x v))
      (ordinaryHostResources (ordinaryExpansionRim C z o x y) (ordinaryExpansionSpokes z v u)) := by
  intro e he e' he' hh
  cases e with
  | inl e =>
    cases e' with
    | inr p => cases hh
    | inl e' =>
      rw [Finset.mem_coe,ordinaryHostResources_rim] at he he'
      exact congrArg Sum.inl (ordinaryExpansion_attachment_rim_injective C z o hzo x y v hxy he he' (Sum.inl.inj hh))
  | inr p =>
    cases e' with
    | inl e' => cases hh
    | inr q =>
      rcases p with ⟨a,b⟩;rcases q with ⟨c,d⟩
      rw [Finset.mem_coe,ordinaryHostResources_spoke] at he he'
      exact congrArg Sum.inr (ordinaryExpansion_attachment_spoke_injective z x v u hvu he he' (Sum.inr.inj hh))

theorem actual_expansion_attachment_bijection
    (G : SimpleGraph V) (H : V → U → Prop) (C : SimpleGraph W) (z o : W) (hzo : C.Adj z o) :
    let E := G.edgeFinset
    let J := {e : V×U // H e.1 e.2}
    let x := fun e : E => e.val.out.1
    let y := fun e : E => e.val.out.2
    let v := fun j : J => j.val.1
    let u := fun j : J => j.val.2
    let S := ordinaryHostResources (ordinaryExpansionRim C z o x y) (ordinaryExpansionSpokes z v u)
    let T := ordinaryHostResources (ordinaryAttachmentRim G C z (expansionAttachmentRoots x v))
      (ordinaryAttachmentSpokes H z (expansionAttachmentRoots x v))
    let f := attachmentResourceMap (U:=U) z (expansionAttachmentRoots x v)
    Set.InjOn f S ∧ S.image f=T := by
  dsimp only
  have hout (e : G.edgeFinset) : s(e.val.out.1,e.val.out.2)=e.val := by
    rw [Sym2.mk];exact e.val.out_eq
  have hxy : Function.Injective (fun e : G.edgeFinset => s(e.val.out.1,e.val.out.2)) := by
    intro e e' he
    apply Subtype.ext
    simpa only [hout] using he
  have hvu : Function.Injective (fun j : {e : V×U // H e.1 e.2} => (j.val.1,j.val.2)) := by
    intro j j' h
    exact Subtype.ext h
  have hGc : ∀ a b,G.Adj a b → ∃ e : G.edgeFinset,s(e.val.out.1,e.val.out.2)=s(a,b) := by
    intro a b hab
    exact ⟨⟨s(a,b),SimpleGraph.mem_edgeFinset.mpr hab⟩,hout _⟩
  have hHc : ∀ a b,H a b → ∃ j : {e : V×U // H e.1 e.2},j.val.1=a ∧ j.val.2=b := by
    intro a b hab
    exact ⟨⟨(a,b),hab⟩,rfl,rfl⟩
  refine ⟨ordinaryExpansion_attachment_resources_injective C z o hzo.ne _ _ _ _ hxy hvu,?_⟩
  have hh := ordinaryExpansion_attachment_resources_image (J:={e : V×U // H e.1 e.2}) G H C z o hzo
      (fun e : G.edgeFinset => e.val.out.1) (fun e : G.edgeFinset => e.val.out.2)
      (fun j => j.val.1) (fun j => j.val.2) (edge_out_adj G) (fun j => j.property) hGc hHc
  ext e
  simpa only [Finset.mem_image] using Finset.ext_iff.mp hh e

end Oberwolfach
