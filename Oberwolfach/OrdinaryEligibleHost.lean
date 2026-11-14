module

public import Oberwolfach.OrdinaryShiftedActiveFiberNormalization
public import Oberwolfach.RawPhysicalCuts

@[expose] public section
/-! The manuscript's physical eligibility is obtained by removing a
bounded-degree permutation conflict graph from the original host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def ordinaryEligibleHost (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ):SimpleGraph V:=
  P\permutationConflictGraph π (3*d+2)

theorem ordinary_eligible_host_adj (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (x y:V):
    (ordinaryEligibleHost P π d).Adj x y ↔ P.Adj x y ∧ ¬PermutationClose π (3*d+2) x y :=by
  change P.Adj x y ∧ ¬(permutationConflictGraph π (3*d+2)).Adj x y ↔ _
  constructor
  · rintro ⟨h,hnot⟩
    exact ⟨h,fun hc=>hnot ⟨h.ne,hc⟩⟩
  · rintro ⟨h,hnot⟩
    exact ⟨h,fun hc=>hnot hc.2⟩

theorem ordinary_eligible_host_degree (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (x:V):
    (ordinaryEligibleHost P π d).degree x≤P.degree x ∧
      P.degree x≤(ordinaryEligibleHost P π d).degree x+(6*d+4) :=by
  constructor
  · have hs:(ordinaryEligibleHost P π d).neighborFinset x⊆P.neighborFinset x:=by
      intro y hy
      simp only [SimpleGraph.mem_neighborFinset] at hy ⊢
      exact (ordinary_eligible_host_adj P π d x y).mp hy |>.1
    have hh:=Finset.card_le_card hs
    simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hh
  · have hh:=graph_degree_le_sdiff_add P (permutationConflictGraph π (3*d+2)) x
    have hc:=permutationConflictGraph_degree_le π (3*d+2) x
    have hh':P.degree x≤(ordinaryEligibleHost P π d).degree x+(permutationConflictGraph π (3*d+2)).degree x:=by
      convert hh using 1 <;> congr! 4 <;> exact Subsingleton.elim _ _
    omega

theorem ordinary_eligible_host_state (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (g:Γ) (j:Color) (raw:RawMarkedOutcome V U Γ Color):
    physicallyRestrictedState (ordinaryMixedPhysicalResource (U:=U) π)
      (ordinaryPhysicalEligible (U:=U) π d)
      (typedMarkedResourceState (ordinaryShiftedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j))=
    typedMarkedResourceState (ordinaryShiftedPairRims (ordinaryEligibleHost P π d) π d raw)
      (rawMarkedPairSpokes π d raw g j) :=by
  funext z
  cases z with
  | inr a=>simp [physicallyRestrictedState,ordinaryMixedPhysicalResource,ordinaryPhysicalEligible,typedMarkedResourceState]
  | inl e=>
    cases e with
    | inl xy=>
      simp only [physicallyRestrictedState,ordinaryMixedPhysicalResource,Sum.elim_inl,
        ordinaryPhysicalEligible,markedPairPhysical,typedMarkedResourceState,decide_eq_true_eq,
        ordinaryShiftedPairRims,ordinary_eligible_host_adj,SimpleGraph.mem_edgeFinset]
      by_cases h:P.Adj xy.1 xy.2
      · have hn:xy.1≠xy.2:=h.ne
        simp [permutationConflictGraph,h,hn,Bool.and_assoc,Bool.and_comm,Bool.and_left_comm]
      · simp [h]
    | inr xy=>
      simp only [physicallyRestrictedState,ordinaryMixedPhysicalResource,Sum.elim_inl,Sum.elim_inr,
        ordinaryPhysicalEligible,markedPairPhysical,typedMarkedResourceState,decide_eq_true_eq,
        ordinaryShiftedPairRims,ordinary_eligible_host_adj,SimpleGraph.mem_edgeFinset]
      by_cases h:P.Adj xy.1 (π xy.2)
      · have hn:xy.1≠π xy.2:=h.ne
        simp [permutationConflictGraph,h,hn,Bool.and_assoc,Bool.and_comm,Bool.and_left_comm]
      · simp [h]
end Oberwolfach
