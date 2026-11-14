module

public import Oberwolfach.OrdinaryMixedSomePayload
public import Oberwolfach.MixedApproximateResourceAggregation

@[expose] public section
/-! Extraction preserves the original mixed candidate's index and its
unmarked resource set exactly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V U CM:Type} {CO:I→Type} [Fintype I] [Fintype V] [Fintype U]
  [LinearOrder V] [DecidableEq U] [Fintype CM] [∀i,Fintype (CO i)]

theorem ordinary_mixed_some_payload_index
    (x:{c:Σj,OrdinaryMixedGenericFamily CM CO j // c.1.isSome}) (i₀:I):
    x.val.1.getD i₀=(ordinaryMixedSomePayload x).1 :=by
  have hh:=ordinary_mixed_some_payload_original x
  have hi:=congrArg Sigma.fst hh
  rw [hi]
  rfl

theorem ordinary_mixed_some_payload_resources
    (RM:CM→Finset (((V×V)⊕(V×V))⊕(Bool×V×U)))
    (RO:∀i,CO i→Finset ((V×V)⊕(V×U)))
    (x:{c:Σj,OrdinaryMixedGenericFamily CM CO j // c.1.isSome}):
    mixedCandidateResources (ordinaryMixedGenericResources RM RO) x.val =
      (RO (ordinaryMixedSomePayload x).1 (ordinaryMixedSomePayload x).2).map ordinaryMarkedResourceEmbedding :=by
  rw [ordinary_mixed_some_payload_original x]
  rfl
end Oberwolfach
