module

public import Oberwolfach.OrdinaryPhysicalUnmarkedMatching
public import Oberwolfach.TypedMarkedLoadBounds

@[expose] public section
/-! Every ordinary tuple selected by the physical matching uses sampled rim
arcs and ordinary spokes at its own hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_physical_unmarked_payload_sampled (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (R:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop) (H:Bool→Fin n→U→Prop):
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState R H;
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources
      (ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W))) state))
    (u:U) (a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u),
    let W:=(ordinaryPhysicalUnmarkedPayload π d m RM state L u a).2;
    (∀j,H false (W.1.val j) u) ∧
    (∀j,R (Sum.inl (W.1.val j,W.1.val (cycleNext j)))) :=by
  intro RM state L u a W
  have hhub:W.2=u:=ordinary_physical_unmarked_payload_hub π d m RM state L u a
  have heq:=ordinary_mixed_some_payload_resources RM
    (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    ⟨a.val.val,(Finset.mem_filter.mp a.property).2.1⟩
  have hactive:∀x∈(orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding,state x=true:=by
    intro x hx
    have hx':x∈mixedCandidateResources (ordinaryMixedGenericResources RM
      (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)) a.val.val:=by
      rw [heq]
      exact hx
    exact a.val.property x hx'
  constructor
  · intro j
    have hm:Sum.inr (W.1.val j,W.2)∈orderedOrdinaryResources W:=
      (orderedOrdinaryResources_spoke W _).2 ⟨j,rfl⟩
    have hh:=hactive _ (Finset.mem_map.mpr ⟨_,hm,rfl⟩)
    simpa only [state,Function.Embedding.coeFn_mk,ordinaryMarkedResourceEmbedding,orderedOrdinaryResourceEmbedding,typedMarkedResourceState,
      Sum.elim_inr,decide_eq_true_eq,hhub] using hh
  · intro j
    have hm:Sum.inl (W.1.val j,W.1.val (cycleNext j))∈orderedOrdinaryResources W:=
      (orderedOrdinaryResources_rim W _).2 ⟨j,rfl⟩
    have hh:=hactive _ (Finset.mem_map.mpr ⟨_,hm,rfl⟩)
    simpa only [state,Function.Embedding.coeFn_mk,ordinaryMarkedResourceEmbedding,orderedOrdinaryResourceEmbedding,typedMarkedResourceState,
      Sum.elim_inl,decide_eq_true_eq] using hh
end Oberwolfach
