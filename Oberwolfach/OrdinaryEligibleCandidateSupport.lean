module

public import Oberwolfach.OrdinaryEligibleHost
public import Oberwolfach.RawMarkedCandidateGeometry
public import Oberwolfach.PhysicalOrdinaryTupleWeight
public import Oberwolfach.OrdinaryShiftedUnmarkedLoadBridge

@[expose] public section
/-! Wheels supported on the eligible host use only permitted physical
resources, for both the shifted and the unshifted construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {m b:ℕ} {π:Equiv.Perm V} {H₀ Hₖ:V→U→Prop}

theorem ordinary_eligible_host_edge_allowed (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (x y:V)
    (h:(ordinaryEligibleHost P π d).Adj x y):
    ordinaryPhysicalEligible (U:=U) π d (Sum.inl s(x,y)) :=by
  change s(x,y)∉(permutationConflictGraph π (3*d+2)).edgeFinset
  intro he
  exact (ordinary_eligible_host_adj P π d x y).mp h |>.2 ((SimpleGraph.mem_edgeFinset.mp he).2)

theorem ordinary_shifted_candidate_resources_eligible
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m b:ℕ)
    (W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π b H₀ Hₖ)
    (hP:∀i:Fin m,(ordinaryEligibleHost P π d).Adj (W.1.val i.castSucc) (W.1.val i.succ))
    (hK:(ordinaryEligibleHost P π d).Adj (W.1.val (Fin.last m)) (π (W.1.val 0))):
    ∀z∈typedMarkedOccurrenceResources W,ordinaryPhysicalEligible (U:=U) π d (ordinaryMixedPhysicalResource π z) :=by
  intro z hz
  cases z with
  | inr z=>simp [ordinaryMixedPhysicalResource,ordinaryPhysicalEligible]
  | inl e=>
    obtain ⟨i,hi⟩:=(typedMarkedOccurrenceResources_rim W e).mp hz
    revert hi
    refine Fin.lastCases ?_ (fun j=>?_) i
    · intro hi
      have he:e=Sum.inr (W.1.val (Fin.last m),W.1.val 0):=by
        rw [←hi,markedPairCycle_edge_marked]
      rw [he]
      exact ordinary_eligible_host_edge_allowed P π d _ _ hK
    · intro hi
      have he:e=Sum.inl (W.1.val j.castSucc,W.1.val j.succ):=by
        rw [←hi,markedPairCycle_edge_ordinary]
      rw [he]
      exact ordinary_eligible_host_edge_allowed P π d _ _ (hP j)

theorem ordinary_unshifted_candidate_resources_eligible
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r b:ℕ)
    (W:OrderedOrdinaryWheel (U:=U) π b r)
    (hP:∀i:Fin r,(ordinaryEligibleHost P π d).Adj (W.1.val i) (W.1.val (cycleNext i))):
    ∀z∈(orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding,
      ordinaryPhysicalEligible (U:=U) π d (ordinaryMixedPhysicalResource π z) :=by
  intro z hz
  obtain ⟨z',hz',rfl⟩:=Finset.mem_map.mp hz
  cases z' with
  | inr e=>simp [ordinaryMixedPhysicalResource,ordinaryPhysicalEligible,ordinaryMarkedResourceEmbedding,
      Function.Embedding.coeFn_mk,orderedOrdinaryResourceEmbedding]
  | inl e=>
    obtain ⟨i,hi⟩:=(orderedOrdinaryResources_rim W e).mp hz'
    have he:e=(W.1.val i,W.1.val (cycleNext i)):=hi.symm
    rw [he]
    exact ordinary_eligible_host_edge_allowed P π d _ _ (hP i)
end Oberwolfach
