module

public import Oberwolfach.BufferedCompletionImageCover

@[expose] public section
/-! Reserved labels survive as ordinary residual spokes unless they occur
in the actual completion image. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_buffered_reserved_protection
    {X V I:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V] [Fintype I]
    (n:I→ℕ) (inner:∀i,Fin (n i+1)↪X)
    (Old Remaining:Finset X) (ψ:X→V) (Φ:{x // x∈Remaining}→V)
    (fC:{x // x∉bufferedPathStrictInterior n inner}↪V)
    (hcover:Old∪Remaining=Finset.univ)
    (hold:∀x:{x // x∉bufferedPathStrictInterior n inner},x.val∈Old→fC x=ψ x.val)
    (hnew:∀x:{x // x∈Remaining},∀hx:x.val∉bufferedPathStrictInterior n inner,fC ⟨x.val,hx⟩=Φ x)
    (L B Y:Finset V)
    (hOldAvoid:Disjoint ((Old\bufferedPathStrictInterior n inner).image ψ) L)
    (hBAvoid:Disjoint B L) (hYAvoid:Disjoint Y L):
    ∀v,v∈L→v∉Finset.univ.image Φ→
      v∈(Finset.univ\(outsideBufferedPathImage n inner fC∪B))\Y:=by
  intro v hv hfree
  have hcov:=buffered_completion_image_cover n inner Old Remaining ψ Φ fC hcover hold hnew
  have hOutside:v∉outsideBufferedPathImage n inner fC:=by
    intro h
    rcases Finset.mem_union.mp (hcov h) with hOld|hNew
    · exact (Finset.disjoint_left.mp hOldAvoid) hOld hv
    · exact hfree hNew
  have hB:v∉B:=fun h=>(Finset.disjoint_left.mp hBAvoid) h hv
  have hY:v∉Y:=fun h=>(Finset.disjoint_left.mp hYAvoid) h hv
  simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_union,not_or]
  exact ⟨⟨hOutside,hB⟩,hY⟩
end Oberwolfach
