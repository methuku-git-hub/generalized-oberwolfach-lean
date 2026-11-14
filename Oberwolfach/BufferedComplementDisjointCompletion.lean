module

public import Oberwolfach.BufferedComplementImage
public import Oberwolfach.BufferedPathBoundaryCompletion

@[expose] public section
/-! The ordinary residual complement avoids the whole completion image:
outside vertices and both endpoint families have been excluded. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem buffered_residual_ordinary_disjoint_completion
    {X V I:Type} [Fintype X] [Fintype V] [Fintype I] [DecidableEq X] [DecidableEq V]
    (n:I→ℕ) (inner:∀i,Fin (n i+1)↪X)
    (fC:{x // x∉bufferedPathStrictInterior n inner}→V) (start finish:I→V)
    (hstart:∀i (h:inner i 0∉bufferedPathStrictInterior n inner),fC ⟨inner i 0,h⟩=start i)
    (hfinish:∀i (h:inner i (Fin.last (n i))∉bufferedPathStrictInterior n inner),fC ⟨inner i (Fin.last (n i)),h⟩=finish i):
    Disjoint ((Finset.univ\(outsideBufferedPathImage n inner fC ∪ Finset.univ.image finish))\Finset.univ.image start)
      (Finset.univ.image fC) :=by
  apply Finset.disjoint_left.mpr
  intro v hv himage
  obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp himage
  have hR:=Finset.mem_sdiff.mp hv
  have hnotY:=hR.2
  have hnot:= (Finset.mem_sdiff.mp hR.1).2
  have houtside:fC x∉outsideBufferedPathImage n inner fC:=by
    intro hh
    exact hnot (Finset.mem_union_left _ hh)
  have hfinish':fC x∉Finset.univ.image finish:=by
    intro hh
    exact hnot (Finset.mem_union_right _ hh)
  by_cases hx:x.val∈bufferedPathFullDomain n inner
  · obtain ⟨i,hi|hi⟩:=buffered_path_boundary_is_endpoint n inner x.val hx x.property
    · have he:fC x=start i:=by
        have hx':x=⟨inner i 0,by simpa only [←hi] using x.property⟩:=Subtype.ext hi
        rw [hx']
        exact hstart i _
      exact hnotY (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he.symm⟩)
    · have he:fC x=finish i:=by
        have hx':x=⟨inner i (Fin.last (n i)),by simpa only [←hi] using x.property⟩:=Subtype.ext hi
        rw [hx']
        exact hfinish i _
      exact hfinish' (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he.symm⟩)
  · exact houtside (outside_buffered_path_image_mem n inner fC x.val x.property hx)
end Oberwolfach
