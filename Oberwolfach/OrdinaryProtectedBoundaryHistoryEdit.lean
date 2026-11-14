module

public import Oberwolfach.OrdinaryProtectedBoundaryHistory
public import Oberwolfach.OrdinaryProtectedBoundaryEdit

@[expose] public section
/-! On a nested later region the older protected deletions vanish, while the
most recent deletion changes the next boundary by its recorded cost. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_nested_protected_boundary_history_edit
    (Q:SimpleGraph V) (H:V→U→Prop) (R:I→SimpleGraph V) (S:I→V→U→Prop)
    (D:SimpleGraph V) (E:V→U→Prop) (X T:Finset V) (Z W:Finset U)
    (Told:I→Finset V) (Wold:I→Finset U) (cost:ℝ)
    (hX:∀i,X⊆Told i) (hZ:∀i,Z⊆Wold i)
    (havoid:∀i,Disjoint (ordinaryPhysicalGraph (R i) (S i)) (ordinaryDeepBlocker (Told i) (Wold i)))
    (hcost:∀w:V⊕U,((spanningRestriction (ordinaryBoundaryGraph D E T W)
      (ordinaryInnerVertices X Z)).degree w:ℝ)≤cost):
    let C:=⨆i,ordinaryPhysicalGraph (R i) (S i);
    let G:=spanningRestriction (ordinaryBoundaryGraph Q H T W) (ordinaryInnerVertices X Z);
    let G':=spanningRestriction
      (ordinaryBoundaryGraph ((Q\C.comap Sum.inl)\(ordinaryPhysicalGraph D E).comap Sum.inl)
        (ordinarySpokesAfterPhysicalDeletion (ordinarySpokesAfterPhysicalDeletion H C) (ordinaryPhysicalGraph D E)) T W)
      (ordinaryInnerVertices X Z);
    ∀w:V⊕U,((changed (G.neighborFinset w) (G'.neighborFinset w)).card:ℝ)≤cost:=by
  intro C G G'
  let B:=spanningRestriction (ordinaryBoundaryGraph (Q\D) (fun v u=>H v u∧¬E v u) T W)
      (ordinaryInnerVertices X Z)
  have he:G'=B:=by
    have hh:=ordinary_nested_protected_boundary_after_two_deletions Q H R S (ordinaryPhysicalGraph D E)
      X T Z W Told Wold hX hZ havoid
    convert hh using 1 <;> rfl
  intro w
  have hb:=ordinary_protected_boundary_edit Q D H E X T Z W cost hcost w
  rw [he]
  convert hb using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
