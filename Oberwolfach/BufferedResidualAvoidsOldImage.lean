module

public import Oberwolfach.BufferedComplementDisjointCompletion

@[expose] public section
/-! The actual old-domain image is part of the completion image, hence it is
avoided by the residual ordinary spokes. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem buffered_residual_ordinary_avoids_old_image
    {X V I:Type} [Fintype X] [Fintype V] [Fintype I] [DecidableEq X] [DecidableEq V]
    (n:I→ℕ) (inner:∀i,Fin (n i+1)↪X)
    (fC:{x // x∉bufferedPathStrictInterior n inner}→V) (start finish:I→V)
    (hstart:∀i (h:inner i 0∉bufferedPathStrictInterior n inner),fC ⟨inner i 0,h⟩=start i)
    (hfinish:∀i (h:inner i (Fin.last (n i))∉bufferedPathStrictInterior n inner),fC ⟨inner i (Fin.last (n i)),h⟩=finish i)
    (Old:Finset X) (ψ:X→V)
    (hOld:∀x (hx:x∈Old) (h:x∉bufferedPathStrictInterior n inner),fC ⟨x,h⟩=ψ x):
    Disjoint ((Finset.univ\(outsideBufferedPathImage n inner fC ∪ Finset.univ.image finish))\Finset.univ.image start)
      ((Old\bufferedPathStrictInterior n inner).image ψ) :=by
  have hsub:(Old\bufferedPathStrictInterior n inner).image ψ⊆Finset.univ.image fC:=by
    intro v hv
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hv
    obtain ⟨hxOld,hxInt⟩:=Finset.mem_sdiff.mp hx
    exact Finset.mem_image.mpr ⟨⟨x,hxInt⟩,Finset.mem_univ _,hOld x hxOld hxInt⟩
  exact (buffered_residual_ordinary_disjoint_completion n inner fC start finish hstart hfinish).mono_right hsub

theorem buffered_residual_ordinary_avoids_old_image_of_superset
    {X V I:Type} [Fintype X] [Fintype V] [Fintype I] [DecidableEq X] [DecidableEq V]
    (n:I→ℕ) (inner:∀i,Fin (n i+1)↪X)
    (fC:{x // x∉bufferedPathStrictInterior n inner}→V) (start finish:I→V)
    (hstart:∀i (h:inner i 0∉bufferedPathStrictInterior n inner),fC ⟨inner i 0,h⟩=start i)
    (hfinish:∀i (h:inner i (Fin.last (n i))∉bufferedPathStrictInterior n inner),fC ⟨inner i (Fin.last (n i)),h⟩=finish i)
    (Old:Finset X) (ψ:X→V)
    (hOld:∀x (hx:x∈Old) (h:x∉bufferedPathStrictInterior n inner),fC ⟨x,h⟩=ψ x)
    (Y:Finset V) (hY:Finset.univ.image start⊆Y):
    Disjoint ((Finset.univ\(outsideBufferedPathImage n inner fC ∪ Finset.univ.image finish))\Y)
      ((Old\bufferedPathStrictInterior n inner).image ψ) :=by
  apply (buffered_residual_ordinary_avoids_old_image n inner fC start finish hstart hfinish Old ψ hOld).mono_left
  intro x hx
  obtain ⟨hx,hnot⟩:=Finset.mem_sdiff.mp hx
  exact Finset.mem_sdiff.mpr ⟨hx,fun hy=>hnot (hY hy)⟩
end Oberwolfach
