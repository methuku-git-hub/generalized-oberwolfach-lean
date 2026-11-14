module

public import Oberwolfach.LongRawAssignedPartialGraphEmbeddings
public import Oberwolfach.RawOrdinarySeedPhysicalResources

@[expose] public section
/-! Each rim relation of a selected ordinary raw wheel is one of that
wheel's physical rim resources, with orientation forgotten. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U X:Type} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]

theorem long_raw_selected_rim_physical_resource
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ) (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e))
    (a:LongRawSelectedOrdinary π d m ℓ e M) (x y:Fin n)
    (h:longRawSelectedRimRelation π d m ℓ e M a x y):
    Sum.inl ({x,y}:Finset (Fin n))∈ordinaryWheelPhysicalResources
      (longRawSelectedOrdinaryWheel π d m ℓ e M a).val :=by
  unfold ordinaryWheelPhysicalResources
  simp only [Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and]
  obtain ⟨i,h|h⟩:=h
  · left
    refine ⟨i,?_⟩
    rw [h.1,h.2]
    congr 1
    ext z
    simp
  · left
    refine ⟨i,?_⟩
    rw [h.1,h.2]
    congr 1
    ext z
    simp [or_comm]
end Oberwolfach
