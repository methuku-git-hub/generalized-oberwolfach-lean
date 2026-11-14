module

public import Oberwolfach.OrdinaryProtectedDeletionHistory

@[expose] public section
/-! Only the specified recent deletions can affect a protected inner pair;
    its total deletion degree is at most the sum of their individual costs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_deletion_history_inner_window_degree
    (R:ℕ→SimpleGraph V) (S:ℕ→V→U→Prop) (n:ℕ)
    (X:Finset V) (Z:Finset U) (J:Finset ℕ) (cost:ℕ→ℝ)
    (hzero:∀j<n,j∉J→spanningRestriction (ordinaryPhysicalGraph (R j) (S j))
      (ordinaryInnerVertices X Z)=⊥)
    (hcost:∀j∈J,∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph (R j) (S j))
      (ordinaryInnerVertices X Z)).degree w:ℝ)≤cost j):
    ∀w:V⊕U,((spanningRestriction (ordinaryDeletionHistory R S n)
      (ordinaryInnerVertices X Z)).degree w:ℝ)≤∑j∈J,cost j :=by
  intro w
  let D:=spanningRestriction (ordinaryDeletionHistory R S n) (ordinaryInnerVertices X Z)
  let Dj:=fun j=>spanningRestriction (ordinaryPhysicalGraph (R j) (S j)) (ordinaryInnerVertices X Z)
  have hsub:D.neighborFinset w⊆J.biUnion (fun j=>(Dj j).neighborFinset w):=by
    intro v hv
    have hadj:D.Adj w v:=(D.mem_neighborFinset w v).mp hv
    have hparts:=(spanningRestriction_adj _ _ _ _).mp hadj
    obtain ⟨j,hjn,hjedge⟩:=(ordinary_deletion_history_adj R S n w v).mp hparts.1
    have hjmem:j∈J:=by
      by_contra hjnot
      have hh:(Dj j).Adj w v:=(spanningRestriction_adj _ _ _ _).mpr ⟨hjedge,hparts.2.1,hparts.2.2⟩
      dsimp only [Dj] at hh
      rw [hzero j hjn hjnot] at hh
      exact hh
    apply Finset.mem_biUnion.mpr
    refine ⟨j,hjmem,?_⟩
    exact (SimpleGraph.mem_neighborFinset _ _ _).mpr ((spanningRestriction_adj _ _ _ _).mpr ⟨hjedge,hparts.2.1,hparts.2.2⟩)
  have hnat:D.degree w≤∑j∈J,(Dj j).degree w:=by
    calc
      _ = (D.neighborFinset w).card := (SimpleGraph.card_neighborFinset_eq_degree _ _).symm
      _ ≤ (J.biUnion (fun j=>(Dj j).neighborFinset w)).card := Finset.card_le_card hsub
      _ ≤ ∑j∈J,((Dj j).neighborFinset w).card := Finset.card_biUnion_le
      _ = ∑j∈J,(Dj j).degree w := by simp only [SimpleGraph.card_neighborFinset_eq_degree]
  have hreal:(D.degree w:ℝ)≤∑j∈J,((Dj j).degree w:ℝ):=by exact_mod_cast hnat
  exact hreal.trans (Finset.sum_le_sum (fun j hj=>hcost j hj w))
end Oberwolfach
