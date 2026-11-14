module

public import Oberwolfach.RawMarkedWheelInterval
public import Oberwolfach.MarkedWheelResources

@[expose] public section
/-! At a common hub, physically disjoint marked wheels use different
marked labels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [DecidableEq V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ Hₖ:V→U→Prop}

theorem disjoint_marked_wheels_distinct_marked_labels
    (W₁ W₂:MarkedWheel tail head ktail khead m π b H₀ Hₖ)
    (hdis:Disjoint (markedWheelPhysicalResources W₁) (markedWheelPhysicalResources W₂))
    (hhub:W₁.2.val=W₂.2.val):W₁.1.val 0≠W₂.1.val 0:=by
  intro heq
  have h₁:Sum.inr (W₁.1.val 0,W₁.2.val)∈markedWheelPhysicalResources W₁:=by
    apply (markedWheelPhysicalResources_spoke W₁ _ _).mpr
    refine ⟨rfl,?_⟩
    exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩
  have h₂:Sum.inr (W₁.1.val 0,W₁.2.val)∈markedWheelPhysicalResources W₂:=by
    apply (markedWheelPhysicalResources_spoke W₂ _ _).mpr
    refine ⟨hhub.symm,?_⟩
    apply Finset.mem_image.mpr
    exact ⟨0,Finset.mem_univ _,heq.symm⟩
  exact (Finset.disjoint_left.mp hdis) h₁ h₂
end Oberwolfach

namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [DecidableEq V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ Hₖ:V→U→Prop}

theorem disjoint_marked_wheels_distinct_interval_positions
    (W₁ W₂:MarkedWheel tail head ktail khead m π b H₀ Hₖ)
    (hdis:Disjoint (markedWheelPhysicalResources W₁) (markedWheelPhysicalResources W₂))
    (hhub:W₁.2.val=W₂.2.val) (a b':V) (i j:ℕ)
    (h₁:(π^i) a=W₁.1.val 0) (h₂:(π^j) b'=W₂.1.val 0):
    (a,i)≠(b',j) :=by
  intro he
  have ⟨ha,hi⟩:=Prod.mk.inj he
  subst b'
  subst j
  exact disjoint_marked_wheels_distinct_marked_labels W₁ W₂ hdis hhub (h₁.symm.trans h₂)
end Oberwolfach
