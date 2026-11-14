module

public import Oberwolfach.OrdinaryMixedPhysicalResourceFiber
public import Oberwolfach.OrderedOrdinaryRootGeometry
public import Oberwolfach.MarkedOrdinaryResourceLoads

@[expose] public section
/-! The unshifted wheel's typed resources are physically distinct within
each candidate, including after the common marked-universe embedding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {r b:ℕ} {π:Equiv.Perm V}

theorem ordinary_unshifted_candidate_physical_injective
    (hr:3≤r) (W:OrderedOrdinaryWheel (U:=U) π b r):
    Set.InjOn (ordinaryMixedPhysicalResource (U:=U) π)
      (↑((orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding):
        Set (((V×V)⊕(V×V))⊕(Bool×V×U))) :=by
  intro a ha z hz h
  obtain ⟨a',ha',rfl⟩:=Finset.mem_map.mp ha
  obtain ⟨z',hz',rfl⟩:=Finset.mem_map.mp hz
  apply congrArg ordinaryMarkedResourceEmbedding
  cases a' with
  | inl a=>
    cases z' with
    | inl z=>
      have hp:s(a.1,a.2)=s(z.1,z.2):=by
        change Sum.inl s(a.1,a.2) = Sum.inl s(z.1,z.2) at h
        exact Sum.inl.inj h
      by_contra hne
      exact orderedOrdinary_distinct_rims_physical W hr a.1 a.2 z.1 z.2 ha' hz'
        (fun he=>hne (congrArg Sum.inl he)) hp
    | inr z=>simp [ordinaryMixedPhysicalResource,ordinaryMarkedResourceEmbedding,orderedOrdinaryResourceEmbedding] at h
  | inr a=>
    cases z' with
    | inl z=>simp [ordinaryMixedPhysicalResource,ordinaryMarkedResourceEmbedding,orderedOrdinaryResourceEmbedding] at h
    | inr z=>
      have hp:a=z:=by
        change Sum.inr a = Sum.inr z at h
        exact Sum.inr.inj h
      exact congrArg Sum.inr hp
end Oberwolfach
