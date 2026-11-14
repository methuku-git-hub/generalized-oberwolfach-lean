module

public import Oberwolfach.BufferedPathInteriorCompletion

@[expose] public section
/-! The complement vertices outside the reserved paths have a canonical
finite image, and the paper's residual spoke set is disjoint from it. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def outsideBufferedPathImage {X V I:Type*} [Fintype X] [DecidableEq X] [DecidableEq V] [Fintype I]
    (n:I→ℕ) (inner:∀i,Fin (n i+1)↪X)
    (fC:{x // x∉bufferedPathStrictInterior n inner}→V) : Finset V :=
  (Finset.univ.filter (fun x:{x // x∉bufferedPathStrictInterior n inner}=>x.val∉bufferedPathFullDomain n inner)).image fC

theorem outside_buffered_path_image_mem
    {X V I:Type*} [Fintype X] [DecidableEq X] [DecidableEq V] [Fintype I]
    (n:I→ℕ) (inner:∀i,Fin (n i+1)↪X)
    (fC:{x // x∉bufferedPathStrictInterior n inner}→V)
    (x:X) (hx:x∉bufferedPathStrictInterior n inner) (hxA:x∉bufferedPathFullDomain n inner) :
    fC ⟨x,hx⟩∈outsideBufferedPathImage n inner fC := by
  exact Finset.mem_image.mpr ⟨⟨x,hx⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxA⟩,rfl⟩

theorem residual_spoke_set_disjoint_complement
    {V:Type*} [Fintype V] [DecidableEq V] (R Z B:Finset V)
    (hR:R=Finset.univ\(Z∪B)) : Disjoint R Z := by
  rw [hR]
  apply Finset.disjoint_left.mpr
  intro x hx hxZ
  exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_left B hxZ)
end Oberwolfach
