module

public import Oberwolfach.MarkedBoundarySupportEvent
public import Oberwolfach.DirectedBoundaryNeighbourhoods

@[expose] public section

/-! Exact boundary support formulas for the actual rim and spoke
neighbourhoods. Successor images include only row labels, never hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

def markedBoundaryRimNeighbours (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (X:Finset V) (σ:Sym2 (V⊕U)→Bool) (x:V):Finset V :=
  X.filter (fun y=>∃ a:E⊕K,
    ((Sum.elim tail ktail a=x∧Sum.elim head khead a=y)∨
      (Sum.elim head khead a=x∧Sum.elim tail ktail a=y))∧
      σ (ordinaryPhysicalResource (Sum.inl (markedArcPhysicalCoin tail head ktail khead π a)))=true)

def markedBoundarySpokeHubs (H₀ HK:V→U→Prop) (Z:Finset U) (σ:Sym2 (V⊕U)→Bool) (x:V):Finset U :=
  Z.filter (fun u=>(H₀ x u∨HK x u)∧σ s(Sum.inl x,Sum.inr u)=true)
def markedBoundarySpokeRows (H₀ HK:V→U→Prop) (X:Finset V) (σ:Sym2 (V⊕U)→Bool) (u:U):Finset V :=
  X.filter (fun x=>(H₀ x u∨HK x u)∧σ s(Sum.inl x,Sum.inr u)=true)

theorem marked_boundary_neighbours_at_row (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (H₀ HK:V→U→Prop) (X:Finset V) (Z:Finset U) (σ:Sym2 (V⊕U)→Bool) (x:V):
    directedBoundaryNeighbours (markedActiveAuxTail tail ktail H₀ HK) (markedActiveAuxHead head khead H₀ HK)
      (markedActivePhysicalCoin tail head ktail khead π H₀ HK) (ordinaryInnerVertices X Z) σ (Sum.inl x)=
      ordinaryInnerVertices (markedBoundaryRimNeighbours tail head ktail khead π X σ x)
        (markedBoundarySpokeHubs H₀ HK Z σ x) := by
  ext w
  cases w with
  | inl v=>
    simp [directedBoundaryNeighbours,ordinaryInnerVertices_left,markedBoundaryRimNeighbours,
      markedActiveAuxTail,markedActiveAuxHead,markedActivePhysicalCoin,Sum.exists,Subtype.exists]
  | inr u=>
    simp [directedBoundaryNeighbours,ordinaryInnerVertices_right,markedBoundarySpokeHubs,
      markedActiveAuxTail,markedActiveAuxHead,markedActivePhysicalCoin,ordinaryPhysicalResource,
      Sum.exists,Subtype.exists,Prod.exists]

theorem marked_boundary_neighbours_at_hub (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (H₀ HK:V→U→Prop) (X:Finset V) (Z:Finset U) (σ:Sym2 (V⊕U)→Bool) (u:U):
    directedBoundaryNeighbours (markedActiveAuxTail tail ktail H₀ HK) (markedActiveAuxHead head khead H₀ HK)
      (markedActivePhysicalCoin tail head ktail khead π H₀ HK) (ordinaryInnerVertices X Z) σ (Sum.inr u)=
      (markedBoundarySpokeRows H₀ HK X σ u).image Sum.inl := by
  ext w
  cases w with
  | inl v=>
    simp [directedBoundaryNeighbours,ordinaryInnerVertices_left,markedBoundarySpokeRows,
      markedActiveAuxTail,markedActiveAuxHead,markedActivePhysicalCoin,ordinaryPhysicalResource,
      Sum.exists,Subtype.exists,Prod.exists]
  | inr v=>
    simp [directedBoundaryNeighbours,ordinaryInnerVertices_right,markedActiveAuxTail,markedActiveAuxHead,
      Sum.exists,Subtype.exists,Prod.exists]

theorem marked_boundary_support_at_row (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (H₀ HK:V→U→Prop) (X:Finset V) (Z:Finset U) (σ:Sym2 (V⊕U)→Bool) (x:V) (hx:x∉X):
    markedBoundarySupport tail head ktail khead π H₀ HK X Z σ (Sum.inl x)=
      ordinaryInnerVertices
        (markedBoundaryRimNeighbours tail head ktail khead π X σ x∪
          (markedBoundaryRimNeighbours tail head ktail khead π X σ x).image π)
        (markedBoundarySpokeHubs H₀ HK Z σ x) := by
  unfold markedBoundarySupport
  rw [directedBoundarySupport_eq_neighbours _ _ _ _ _ _ _ (by simpa only [ordinaryInnerVertices_left] using hx),
    marked_boundary_neighbours_at_row]
  ext w
  cases w <;> simp [ordinaryInnerVertices,Finset.image_union,Finset.image_image]

theorem marked_boundary_support_at_hub (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (H₀ HK:V→U→Prop) (X:Finset V) (Z:Finset U) (σ:Sym2 (V⊕U)→Bool) (u:U) (hu:u∉Z):
    markedBoundarySupport tail head ktail khead π H₀ HK X Z σ (Sum.inr u)=
      ((markedBoundarySpokeRows H₀ HK X σ u)∪(markedBoundarySpokeRows H₀ HK X σ u).image π).image Sum.inl := by
  unfold markedBoundarySupport
  rw [directedBoundarySupport_eq_neighbours _ _ _ _ _ _ _ (by simpa only [ordinaryInnerVertices_right] using hu),
    marked_boundary_neighbours_at_hub]
  simp [Finset.image_union,Finset.image_image]
  rfl

end Oberwolfach
