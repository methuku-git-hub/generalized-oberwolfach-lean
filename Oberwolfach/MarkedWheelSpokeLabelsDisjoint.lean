module

public import Oberwolfach.MarkedWheelSpokeDisjointness

@[expose] public section
/-! Physical disjointness at one hub separates every spoke label, including
ordinary and marked spokes of distinct selected wheels. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [DecidableEq V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ Hₖ:V→U→Prop}

theorem disjoint_marked_wheels_distinct_spoke_labels
    (W₁ W₂:MarkedWheel tail head ktail khead m π b H₀ Hₖ)
    (hdis:Disjoint (markedWheelPhysicalResources W₁) (markedWheelPhysicalResources W₂))
    (hhub:W₁.2.val=W₂.2.val) (i j:Fin (m+1)):W₁.1.val i≠W₂.1.val j:=by
  intro heq
  have h₁:Sum.inr (W₁.1.val i,W₁.2.val)∈markedWheelPhysicalResources W₁:=by
    apply (markedWheelPhysicalResources_spoke W₁ _ _).mpr
    exact ⟨rfl,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  have h₂:Sum.inr (W₁.1.val i,W₁.2.val)∈markedWheelPhysicalResources W₂:=by
    apply (markedWheelPhysicalResources_spoke W₂ _ _).mpr
    exact ⟨hhub.symm,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,heq.symm⟩⟩
  exact Finset.disjoint_left.mp hdis h₁ h₂
end Oberwolfach
