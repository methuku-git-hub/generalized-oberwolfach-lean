module

public import Oberwolfach.MarkedExpansionHostMaps
public import Oberwolfach.MarkedAttachmentWheelFamilies
public import Oberwolfach.IndexedMarkedRealizationMaps

@[expose] public section

/-! Under the actual attachment coordinates, an expansion maps to the old
graph plus its attached wheels, with the explicit occurrence exchanges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀ V U E K A S:Type} [Fintype V₀] [Fintype U₀]
    [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V₀] [DecidableEq U₀] [DecidableEq V] [DecidableEq U]
    [DecidableEq A] [DecidableEq S]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ}

theorem marked_attachment_realization_row_quotient (G:IndexedMarkedGraph V₀ U₀ A S)
    (f:V₀→V) (C:(A⊕S)→MarkedWheel tail head ktail khead (l+4) π b H₀ HK)
    (hC:∀ i,(C i).1.val (markedAttachmentPosition l G.jr G.js i)=Sum.elim (f∘G.src) (f∘G.row) i):
    markedExpansionHostRows f C∘markedAttachmentRowMap G (l+4) (by omega)=markedExpansionHostRows f C:=by
  funext v
  rcases v with v|⟨a|s,k⟩
  · rfl
  · by_cases hk:k=markedExpansionRimPosition (l+4) (by omega) (G.jr a)
    · subst k
      simpa only [Function.comp_apply,markedAttachmentRowMap,ite_true,markedExpansionHostRows,
        Sum.elim_inl,Sum.elim_inr,markedAttachmentPosition] using (hC (.inl a)).symm
    · simp only [Function.comp_apply,markedAttachmentRowMap,if_neg hk]
  · by_cases hk:k=markedExpansionSpokePosition (l+4) (by omega) (G.js s)
    · subst k
      simpa only [Function.comp_apply,markedAttachmentRowMap,ite_true,markedExpansionHostRows,
        Sum.elim_inl,Sum.elim_inr,markedAttachmentPosition] using (hC (.inr s)).symm
    · simp only [Function.comp_apply,markedAttachmentRowMap,if_neg hk]

theorem marked_attachment_realization_map (G:IndexedMarkedGraph V₀ U₀ A S)
    (f:V₀→V) (g:U₀→U) (C:(A⊕S)→MarkedWheel tail head ktail khead (l+4) π b H₀ HK)
    (hC:∀ i,(C i).1.val (markedAttachmentPosition l G.jr G.js i)=Sum.elim (f∘G.src) (f∘G.row) i):
    (indexedMarkedExpansion G (l+4) (by omega)).map (markedExpansionHostRows f C) (markedExpansionHostHubs g C)=
      ((indexedMarkedWheelExtension G (l+4)).map (markedExpansionHostRows f C) (markedExpansionHostHubs g C)).reindex
        (privateOccurrenceExchange (fun a=>markedExpansionRimPosition (l+4) (by omega) (G.jr a)))
        (privateSpokeExchange (fun s=>markedExpansionSpokePosition (l+4) (by omega) (G.js s))):=by
  let F:=markedExpansionHostRows f C
  let H:=markedExpansionHostHubs g C
  have hF:F∘markedAttachmentRowMap G (l+4) (by omega)=F:=marked_attachment_realization_row_quotient G f C hC
  have he:=congrArg (fun D=>D.map F H) (indexedMarkedExpansion_to_attachment G (l+4) (by omega))
  rw [IndexedMarkedGraph.map_map,hF,Function.comp_id,IndexedMarkedGraph.reindex_map] at he
  change _=((indexedMarkedWheelExtension G (l+4)).map _ id |>.map F H).reindex _ _ at he
  rw [IndexedMarkedGraph.map_map,hF,Function.comp_id] at he
  exact he

end Oberwolfach
