module

public import Oberwolfach.MixedApproximateResourceAggregation
public import Oberwolfach.OrdinaryMixedGenericFamily

@[expose] public section
/-! An unmarked candidate contains only false-coloured spoke coordinates, so
a true-coloured spoke can only be supplied by a marked candidate. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_true_spoke_candidate_is_marked
    {I V U CM:Type} {CO:I→Type} [Fintype I] [Fintype V] [Fintype U]
    [LinearOrder V] [DecidableEq U] [Fintype CM] [∀i,Fintype (CO i)]
    (RM:CM→Finset (((V×V)⊕(V×V))⊕(Bool×V×U)))
    (RO:∀i,CO i→Finset ((V×V)⊕(V×U)))
    (c:Σi,OrdinaryMixedGenericFamily CM CO i) (v:V) (u:U)
    (h:Sum.inr (true,v,u)∈mixedCandidateResources (ordinaryMixedGenericResources RM RO) c):
    c.1=none:=by
  obtain ⟨tag,payload⟩:=c
  cases tag with
  | none=>rfl
  | some i=>
    change Sum.inr (true,v,u)∈(RO i payload).map ordinaryMarkedResourceEmbedding at h
    obtain ⟨a,ha,he⟩:=Finset.mem_map.mp h
    cases a with
    | inl e=>simp [ordinaryMarkedResourceEmbedding,orderedOrdinaryResourceEmbedding] at he
    | inr e=>simp [ordinaryMarkedResourceEmbedding,orderedOrdinaryResourceEmbedding] at he
end Oberwolfach
