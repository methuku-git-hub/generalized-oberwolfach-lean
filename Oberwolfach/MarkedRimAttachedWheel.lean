module

public import Oberwolfach.MarkedCycleAtLastVertex
public import Oberwolfach.MarkedCycleAtOrdinaryVertex
public import Oberwolfach.MarkedCycleFreshHub
public import Oberwolfach.MarkedExpansionPositions

@[expose] public section

/-! Attach a wheel at the ordinary tail of its chosen same-type rim arc.
The distinguished tail is at position one for an ordinary arc and at the
last position for a marked arc. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

theorem marked_cycle_at_rim_position
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl:2≤l) (j:Bool) (W Z:Finset V) (v:V) (hv:v∈Z)
    (hbudget:(W.card:ℝ)+(Z.card+l+12)*(2*b+1)<c):
    ∃ C:MarkedCycleTuple tail head ktail khead (l+4) π b,
      C.val (markedExpansionRimPosition (l+4) (by omega) j)=v∧
      ∀ i,i≠markedExpansionRimPosition (l+4) (by omega) j→
        C.val i∉W∧C.val i∉Z∧∀ z∈Z,¬PermutationClose π b (C.val i) z:=by
  cases j
  · have he:markedExpansionRimPosition (l+4) (by omega) false=(1:Fin (l+5)):=by
      apply Fin.ext;change 1=1%(l+5);rw [Nat.mod_eq_of_lt (by omega)]
    obtain ⟨C,hC,hav,_⟩:=marked_cycle_at_ordinary_vertex Q hl ∅ (by simp) W Z v hv (by simp) hbudget
    exact ⟨C,by simpa only [he] using hC,by simpa only [he] using hav⟩
  · simpa only [markedExpansionRimPosition,ite_true] using marked_cycle_at_last_vertex Q hl W Z v hv hbudget

theorem marked_wheel_at_rim_position_fresh_hub
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl:2≤l) (j:Bool) (W Z:Finset V) (B:Finset U) (v:V) (hv:v∈Z)
    (hbudget:(W.card:ℝ)+(Z.card+l+12)*(2*b+1)<c) (hB:(B.card:ℝ)<ch):
    ∃ C:MarkedWheel tail head ktail khead (l+4) π b H₀ HK,
      C.1.val (markedExpansionRimPosition (l+4) (by omega) j)=v∧C.2.val∉B∧
      ∀ i,i≠markedExpansionRimPosition (l+4) (by omega) j→
        C.1.val i∉W∧C.1.val i∉Z∧∀ z∈Z,¬PermutationClose π b (C.1.val i) z:=by
  obtain ⟨C,hC,hav⟩:=marked_cycle_at_rim_position Q hl j W Z v hv hbudget
  obtain ⟨u,hu,hCu⟩:=marked_cycle_fresh_hub Q C B hB
  exact ⟨⟨C,⟨u,hCu⟩⟩,hC,hu,hav⟩

end Oberwolfach
