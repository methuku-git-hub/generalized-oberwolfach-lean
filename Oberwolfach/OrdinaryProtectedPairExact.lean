module

public import Oberwolfach.OrdinaryRequiredEdgesCovered
public import Oberwolfach.OrdinaryInnerSpokeTargets

@[expose] public section
/-! If the small required graph is covered and the inner reference graph is
    protected, the actual factor-complement remainder agrees with the
    reference on both kinds of edges in the inner pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_protected_pair_exact
    {X:U→Type} [∀u,Fintype (X u)]
    (Target Sample Reference Protect Embedded:SimpleGraph V) (Inner:Finset V) (Hubs:Finset U)
    (Href:V→U→Prop) (f:∀u,X u↪V)
    (hRef:Reference≤Sample) (hRefTarget:Reference≤Target) (hProtect:Protect≤Reference)
    (hInnerProtect:spanningRestriction Reference Inner≤Protect)
    (hEmbedded:Embedded≤Target\Protect)
    (hcover:ordinaryProtectedRequired Target Sample Reference Inner≤Embedded)
    (hAvoid:∀u x,¬Href (f u x) u)
    (hSpokeCover:∀u v,v∈ordinaryInnerSpokeTargets Inner Hubs Href u→∃x,f u x=v):
    (∀v∈Inner,∀w∈Inner,((Target\Embedded).Adj v w ↔ Reference.Adj v w)) ∧
    (∀v∈Inner,∀u∈Hubs,(v∉Set.range (f u) ↔ Href v u)):=by
  constructor
  · intro v hv w hw
    constructor
    · exact ordinary_required_cover_forces_reference_inner Target Sample Reference Protect Embedded Inner hRef hProtect hcover v hv w hw
    · intro hr
      refine ⟨hRefTarget hr,?_⟩
      intro he
      have hp:Protect.Adj v w:=hInnerProtect ((spanningRestriction_adj Reference Inner v w).mpr ⟨hr,hv,hw⟩)
      exact (hEmbedded he).2 hp
  · intro v hv u hu
    constructor
    · intro hnot
      by_contra hn
      have hT:v∈ordinaryInnerSpokeTargets Inner Hubs Href u:=by
        simp [ordinaryInnerSpokeTargets,hu,hv,hn]
      obtain ⟨x,hx⟩:=hSpokeCover u v hT
      exact hnot ⟨x,hx⟩
    · intro h hx
      obtain ⟨x,hx⟩:=hx
      exact hAvoid u x (hx ▸ h)
end Oberwolfach
