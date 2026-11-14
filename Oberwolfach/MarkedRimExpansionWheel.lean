module

public import Oberwolfach.MarkedOrdinaryRimExpansionCycle
public import Oberwolfach.MarkedMarkedRimExpansionCycle
public import Oberwolfach.MarkedCycleFreshHub

@[expose] public section

/-! Construct the private wheel and both crossed arcs for any formal typed
rim occurrence. No old arc, distinct old endpoints, or old-root global
separation is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

theorem marked_rim_expansion_cycle
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl:2≤l) (j:Bool) (W Z:Finset V) (x y:V) (hx:x∈Z) (hy:y∈Z)
    (hbudget:(W.card:ℝ)+(Z.card+l+16)*(2*b+1)<c):
    ∃ C:MarkedCycleTuple tail head ktail khead (l+4) π b,
      markedArcPresent tail head ktail khead j x
        (C.val (finRotate (l+5) (markedExpansionRimPosition (l+4) (by omega) j)))∧
      markedArcPresent tail head ktail khead j
        (C.val (markedExpansionRimPosition (l+4) (by omega) j)) y∧
      ∀ i,C.val i∉W∧C.val i∉Z∧∀ z∈Z,¬PermutationClose π b (C.val i) z:=by
  cases j
  · exact marked_ordinary_rim_expansion_cycle Q hl W Z x y hx hy hbudget
  · simpa only [markedExpansionRimPosition,ite_true,finRotate_last] using
      marked_marked_rim_expansion_cycle Q hl W Z x y hx hy hbudget

theorem marked_rim_expansion_wheel
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl:2≤l) (j:Bool) (W Z:Finset V) (B:Finset U) (x y:V) (hx:x∈Z) (hy:y∈Z)
    (hbudget:(W.card:ℝ)+(Z.card+l+16)*(2*b+1)<c) (hB:(B.card:ℝ)<ch):
    ∃ C:MarkedWheel tail head ktail khead (l+4) π b H₀ HK,
      C.2.val∉B∧
      markedArcPresent tail head ktail khead j x
        (C.1.val (finRotate (l+5) (markedExpansionRimPosition (l+4) (by omega) j)))∧
      markedArcPresent tail head ktail khead j
        (C.1.val (markedExpansionRimPosition (l+4) (by omega) j)) y∧
      ∀ i,C.1.val i∉W∧C.1.val i∉Z∧∀ z∈Z,¬PermutationClose π b (C.1.val i) z:=by
  obtain ⟨C,hxC,hCy,hav⟩:=marked_rim_expansion_cycle Q hl j W Z x y hx hy hbudget
  obtain ⟨u,hu,hCu⟩:=marked_cycle_fresh_hub Q C B hB
  exact ⟨⟨C,⟨u,hCu⟩⟩,hu,hxC,hCy,hav⟩

end Oberwolfach
