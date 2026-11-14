module

public import Oberwolfach.LongRawSelectedRimPhysical

@[expose] public section
/-! The physical edge set of each extracted ordinary wheel is indexed by its
rim positions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U X:Type} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]

def longRawSelectedRimEdges (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e))
    (a:LongRawSelectedOrdinary π d m ℓ e M):Finset (Sym2 (Fin n)):=
  let Q:=longRawSelectedOrdinaryWheel π d m ℓ e M a
  Finset.univ.image (fun i:Fin (ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a).1)=>
    s(Q.val.1.val i,Q.val.1.val (cycleNext i)))

theorem long_raw_selected_rim_relation_edge_mem
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ) (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e))
    (a:LongRawSelectedOrdinary π d m ℓ e M) (x y:Fin n)
    (h:longRawSelectedRimRelation π d m ℓ e M a x y):
    s(x,y)∈longRawSelectedRimEdges π d m ℓ e M a :=by
  obtain ⟨i,h|h⟩:=h
  · apply Finset.mem_image.mpr
    exact ⟨i,Finset.mem_univ _,by rw [h.1,h.2]⟩
  · apply Finset.mem_image.mpr
    exact ⟨i,Finset.mem_univ _,by rw [h.1,h.2];exact Sym2.eq_swap⟩

theorem long_raw_selected_rim_edge_is_physical_resource
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ) (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e))
    (a:LongRawSelectedOrdinary π d m ℓ e M) (edge:Sym2 (Fin n))
    (h:edge∈longRawSelectedRimEdges π d m ℓ e M a):
    Sum.inl edge.toFinset∈ordinaryWheelPhysicalResources (longRawSelectedOrdinaryWheel π d m ℓ e M a).val :=by
  obtain ⟨i,_,hi⟩:=Finset.mem_image.mp h
  have hr:longRawSelectedRimRelation π d m ℓ e M a
      ((longRawSelectedOrdinaryWheel π d m ℓ e M a).val.1.val i)
      ((longRawSelectedOrdinaryWheel π d m ℓ e M a).val.1.val (cycleNext i)):=
    ⟨i,Or.inl ⟨rfl,rfl⟩⟩
  have hp:=long_raw_selected_rim_physical_resource π d m ℓ e M a _ _ hr
  rw [←hi]
  simpa only [Sym2.toFinset_mk_eq] using hp
end Oberwolfach
