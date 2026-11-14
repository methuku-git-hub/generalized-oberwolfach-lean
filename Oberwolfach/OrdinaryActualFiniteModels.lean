module

public import Oberwolfach.OrdinaryAttachmentResourceMaps
public import Oberwolfach.OrdinaryExpansionRootCounts
public import Oberwolfach.OrdinaryAmbientResourceMaps
public import Oberwolfach.OrdinaryTransformerMapInputs

@[expose] public section

/-! The finite expansion and attachment maps for actual graph edges,
transported to the embedded graph pairs in the common ambient host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀ W V U : Type}
    [Fintype V₀] [Fintype U₀] [Fintype W] [Fintype V] [Fintype U]
    [DecidableEq V₀] [DecidableEq U₀] [DecidableEq W] [DecidableEq V] [DecidableEq U]

abbrev ActualSpoke (H : V₀ → U₀ → Prop) := {e:V₀×U₀ // H e.1 e.2}
abbrev ActualExpansionRow (G : SimpleGraph V₀) (H : V₀ → U₀ → Prop) (W : Type) :=
  ExpansionRow V₀ G.edgeFinset (ActualSpoke H) W
abbrev ActualExpansionHub (G : SimpleGraph V₀) (H : V₀ → U₀ → Prop) :=
  ExpansionHub U₀ G.edgeFinset (ActualSpoke H)

abbrev actualExpansionRim (G : SimpleGraph V₀) (H : V₀ → U₀ → Prop) (C : SimpleGraph W) (z o : W) :=
  ordinaryExpansionRim (J:=ActualSpoke H) C z o
    (fun e:G.edgeFinset => e.val.out.1) (fun e:G.edgeFinset => e.val.out.2)
abbrev actualExpansionSpokes (G : SimpleGraph V₀) (H : V₀ → U₀ → Prop) (z : W) :=
  ordinaryExpansionSpokes (E:=G.edgeFinset) z (fun j:ActualSpoke H => j.val.1) (fun j => j.val.2)
abbrev actualAttachmentRoot (G : SimpleGraph V₀) (H : V₀ → U₀ → Prop) :=
  expansionAttachmentRoots (fun e:G.edgeFinset => e.val.out.1) (fun j:ActualSpoke H => j.val.1)
abbrev actualAttachmentRim (G : SimpleGraph V₀) (H : V₀ → U₀ → Prop) (C : SimpleGraph W) (z : W) :=
  ordinaryAttachmentRim G C z (actualAttachmentRoot G H)
abbrev actualAttachmentSpokes (G : SimpleGraph V₀) (H : V₀ → U₀ → Prop) (z : W) :=
  ordinaryAttachmentSpokes H z (actualAttachmentRoot G H)

theorem actual_embedded_expansion_attachment_bijection
    (G : SimpleGraph V₀) (H : V₀ → U₀ → Prop) (C : SimpleGraph W) (z o : W) (hzo : C.Adj z o)
    (i j : ActualExpansionRow G H W ↪ V) (s t : ActualExpansionHub G H ↪ U) :
    let Q₀ := (actualExpansionRim G H C z o).map i
    let K₀ := ordinaryMappedSpokes (actualExpansionSpokes G H z) i s
    let Q₁ := (actualAttachmentRim G H C z).map j
    let K₁ := ordinaryMappedSpokes (actualAttachmentSpokes G H z) j t
    let f := ordinaryAmbientMap i j (attachmentCollapse z (actualAttachmentRoot G H))
    let g := ordinaryAmbientMap s t id
    Set.InjOn (ordinaryPairResourceMap f g) (ordinaryHostResources Q₀ K₀) ∧
      transformerImageResources Q₀ K₀ f g=ordinaryHostResources Q₁ K₁ ∧
      Function.Injective (fun e:Q₀.edgeFinset => s(f e.val.out.1,f e.val.out.2)) ∧
      Function.Injective (fun e:{p:V×U // K₀ p.1 p.2} => (f e.val.1,g e.val.2)) ∧
      (∀ v w,Q₀.Adj v w → Q₁.Adj (f v) (f w)) ∧ ∀ v u,K₀ v u → K₁ (f v) (g u) := by
  dsimp only
  have hfinite := actual_expansion_attachment_bijection G H C z o hzo
  have h := ordinaryAmbient_resource_bijection
    (actualExpansionRim G H C z o) (actualExpansionSpokes G H z)
    (actualAttachmentRim G H C z) (actualAttachmentSpokes G H z)
    i j s t (attachmentCollapse z (actualAttachmentRoot G H)) id hfinite.1 (by
      ext a
      simpa only [Finset.mem_image, actualExpansionRim, actualExpansionSpokes,
        actualAttachmentRim, actualAttachmentSpokes, actualAttachmentRoot,
        ordinaryPairResourceMap, attachmentResourceMap] using Finset.ext_iff.mp hfinite.2 a)
  exact ⟨h.1,h.2,ordinary_resource_map_rim_injective _ _ _ _ h.1,
    ordinary_resource_map_spoke_injective _ _ _ _ h.1,
    ordinary_resource_image_rim_hom _ _ _ _ _ _ h.2,ordinary_resource_image_spoke_hom _ _ _ _ _ _ h.2⟩

end Oberwolfach
