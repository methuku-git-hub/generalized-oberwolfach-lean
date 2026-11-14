module

public import Oberwolfach.RootWheelCaps

@[expose] public section

/-! Exact root-edge coverage by a family of wheels with prescribed pairs
and distinct hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I : Type*} [Fintype V] [Fintype U] [Fintype I] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ}

theorem root_wheel_family_exact_edges (C:I→OrdinaryWheel Q F H r) (x:V) (v w:I→V) (u:I→U)
    (hvw:∀ i,v i≠w i) (hhub:∀ i,ordinaryWheelHub (C i)=u i)
    (hxv:∀ i,(ordinaryWheelRim (C i)).Adj x (v i))
    (hxw:∀ i,(ordinaryWheelRim (C i)).Adj x (w i)) :
    (∀ a,(wheelFamilyRim C).Adj x a ↔ ∃ i,a=v i∨a=w i) ∧
      (∀ b,wheelFamilySpokes C x b ↔ ∃ i,u i=b) := by
  constructor
  · intro a
    rw [wheelFamilyRim,SimpleGraph.iSup_adj]
    constructor
    · rintro ⟨i,hi⟩
      have hh:=((ordinaryWheelRim (C i)).mem_neighborFinset x a).mpr hi
      rw [ordinaryWheel_root_neighbors (C i) x (v i) (w i) (hvw i) (hxv i) (hxw i)] at hh
      exact ⟨i,by simpa only [Finset.mem_insert,Finset.mem_singleton] using hh⟩
    · rintro ⟨i,he|he⟩
      · exact ⟨i,by rw [he];exact hxv i⟩
      · exact ⟨i,by rw [he];exact hxw i⟩
  · intro b
    constructor
    · rintro ⟨i,hi,hxi⟩
      exact ⟨i,(hhub i).symm.trans hi⟩
    · rintro ⟨i,hi⟩
      exact ⟨i,(hhub i).trans hi,(hxv i).mem_support_left⟩

end Oberwolfach
