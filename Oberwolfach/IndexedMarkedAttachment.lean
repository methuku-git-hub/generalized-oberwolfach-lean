module

public import Oberwolfach.IndexedMarkedExpansionMaps

@[expose] public section

/-! Identifying the old tail with the distinguished private tail changes
an expansion into an attachment, with an explicit permutation of edge
occurrences. The old edge is not lost in this quotient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U A S:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V] [DecidableEq U] [DecidableEq A] [DecidableEq S]

def markedAttachmentRowMap (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m):
    V⊕((A⊕S)×Fin (m+1))→V⊕((A⊕S)×Fin (m+1))
  | .inl v=>.inl v
  | .inr (.inl a,k)=>if k=markedExpansionRimPosition m hm (G.jr a) then .inl (G.src a) else .inr (.inl a,k)
  | .inr (.inr s,k)=>if k=markedExpansionSpokePosition m hm (G.js s) then .inl (G.row s) else .inr (.inr s,k)

def indexedMarkedAttachment (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m):
    IndexedMarkedGraph (V⊕((A⊕S)×Fin (m+1))) (U⊕(A⊕S))
      (A⊕((A⊕S)×Fin (m+1))) (S⊕((A⊕S)×Fin (m+1))):=
  (indexedMarkedWheelExtension G m).map (markedAttachmentRowMap G m hm) id

def IndexedMarkedGraph.reindex (G:IndexedMarkedGraph V U A S) (τ:Equiv.Perm A) (σ:Equiv.Perm S):
    IndexedMarkedGraph V U A S:=
  ⟨G.src∘τ,G.dst∘τ,G.row∘σ,G.hub∘σ,G.jr∘τ,G.js∘σ⟩

theorem indexedMarkedAttachment_balanced (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m)
    (hG:G.IsBalanced m):(indexedMarkedAttachment G m hm).IsBalanced m:=
  IndexedMarkedGraph.map_balanced _ m (indexedMarkedWheelExtension_balanced G m hG) _ _

theorem markedAttachmentRowMap_rim_exchange (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m)
    (a:A⊕((A⊕S)×Fin (m+1))):
    markedAttachmentRowMap G m hm ((indexedMarkedWheelExtension G m).src
      (privateOccurrenceExchange (fun a=>markedExpansionRimPosition m hm (G.jr a)) a))=
    markedAttachmentRowMap G m hm ((indexedMarkedWheelExtension G m).src a):=by
  rcases a with a|⟨a|s,k⟩
  · simp [indexedMarkedWheelExtension,paddingRimTail,markedAttachmentRowMap]
  · by_cases hk:k=markedExpansionRimPosition m hm (G.jr a) <;>
      simp [indexedMarkedWheelExtension,paddingRimTail,markedAttachmentRowMap,hk]
  · rfl

theorem markedAttachmentRowMap_spoke_exchange (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m)
    (s:S⊕((A⊕S)×Fin (m+1))):
    markedAttachmentRowMap G m hm ((indexedMarkedWheelExtension G m).row
      (privateSpokeExchange (fun s=>markedExpansionSpokePosition m hm (G.js s)) s))=
    markedAttachmentRowMap G m hm ((indexedMarkedWheelExtension G m).row s):=by
  rcases s with s|⟨a|s,k⟩
  · simp [indexedMarkedWheelExtension,paddingSpokeRow,markedAttachmentRowMap]
  · rfl
  · by_cases hk:k=markedExpansionSpokePosition m hm (G.js s) <;>
      simp [indexedMarkedWheelExtension,paddingSpokeRow,markedAttachmentRowMap,hk]

theorem indexedMarkedExpansion_to_attachment (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m):
    (indexedMarkedExpansion G m hm).map (markedAttachmentRowMap G m hm) id=
      (indexedMarkedAttachment G m hm).reindex
        (privateOccurrenceExchange (fun a=>markedExpansionRimPosition m hm (G.jr a)))
        (privateSpokeExchange (fun s=>markedExpansionSpokePosition m hm (G.js s))):=by
  apply indexedMarkedGraph_ext
  · funext a;exact (markedAttachmentRowMap_rim_exchange G m hm a).symm
  · rfl
  · funext s;exact (markedAttachmentRowMap_spoke_exchange G m hm s).symm
  · rfl
  · funext a
    exact (privateOccurrenceExchange_preserves_type (fun a=>markedExpansionRimPosition m hm (G.jr a))
      (paddingRimType G.jr m) (fun a=>(markedExpansionRimPosition_type m hm (G.jr a)).symm) a).symm
  · funext s
    exact (privateSpokeExchange_preserves_type (fun s=>markedExpansionSpokePosition m hm (G.js s))
      (paddingSpokeType G.js m) (fun s=>(markedExpansionSpokePosition_type m hm (G.js s)).symm) s).symm

end Oberwolfach
