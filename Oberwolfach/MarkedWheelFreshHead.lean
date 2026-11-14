module

public import Oberwolfach.MarkedCycleAtHead
public import Oberwolfach.MarkedCycleFreshHub

@[expose] public section

/-! Choose a marked wheel through a specified marked head, including its
fresh actual hub. This is an existence construction from host counts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

theorem marked_wheel_at_head_fresh_hub
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl:2≤l) (W Z:Finset V) (B:Finset U) (v:V) (hv:v∈Z)
    (hbudget:(W.card:ℝ)+(Z.card+l+12)*(2*b+1)<c) (hB:(B.card:ℝ)<ch):
    ∃ C:MarkedWheel tail head ktail khead (l+4) π b H₀ HK,
      C.1.val 0=v∧C.2.val∉B∧
      ∀ i:Fin (l+5),i≠0→C.1.val i∉W∧C.1.val i∉Z∧∀ z∈Z,¬PermutationClose π b (C.1.val i) z:=by
  obtain ⟨C,hC,hav,_⟩:=marked_cycle_at_head Q hl ∅ (by simp) W Z v hv (by simp) hbudget
  obtain ⟨u,hu,hCu⟩:=marked_cycle_fresh_hub Q C B hB
  exact ⟨⟨C,⟨u,hCu⟩⟩,hC,hu,hav⟩

end Oberwolfach
