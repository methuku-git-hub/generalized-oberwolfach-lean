module

public import Oberwolfach.BufferedComplementImage

@[expose] public section
/-! The outside complement image is covered by the old embedding and the
actual completion image. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem buffered_completion_image_cover
    {X V I:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V] [Fintype I]
    (n:I→ℕ) (inner:∀i,Fin (n i+1)↪X)
    (Old Remaining:Finset X) (ψ:X→V) (Φ:{x // x∈Remaining}→V)
    (fC:{x // x∉bufferedPathStrictInterior n inner}↪V)
    (hcover:Old∪Remaining=Finset.univ)
    (hold:∀x:{x // x∉bufferedPathStrictInterior n inner},x.val∈Old→fC x=ψ x.val)
    (hnew:∀x:{x // x∈Remaining},∀hx:x.val∉bufferedPathStrictInterior n inner,fC ⟨x.val,hx⟩=Φ x):
    outsideBufferedPathImage n inner fC⊆
      (Old\bufferedPathStrictInterior n inner).image ψ ∪ Finset.univ.image Φ:=by
  intro v hv
  obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hv
  have hxcover:x.val∈Old∪Remaining:=by rw [hcover];exact Finset.mem_univ _
  rcases Finset.mem_union.mp hxcover with ho|hr
  · apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    exact ⟨x.val,Finset.mem_sdiff.mpr ⟨ho,x.property⟩,hold x ho |>.symm⟩
  · apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨⟨x.val,hr⟩,Finset.mem_univ _,?_⟩
    exact (hnew ⟨x.val,hr⟩ x.property).symm
end Oberwolfach
