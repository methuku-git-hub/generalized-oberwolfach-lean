module

public import Oberwolfach.PhysicalRimResourceResidual

@[expose] public section
/-! The residual graph of the surviving resources is exactly the original
rim graph after deleting the forbidden and matched physical edges. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem physical_rim_surviving_residual_eq
    {V U W:Type} [Fintype V] [Fintype U] [Fintype W] [DecidableEq V] [DecidableEq U] [DecidableEq W]
    (φ:W↪Sym2 V⊕(V×U)) (survive:Finset W) (Del:SimpleGraph V)
    (hSurvive:∀w x y,φ w=Sum.inl s(x,y)→(w∈survive↔¬Del.Adj x y))
    (covered:Finset {w // w∈survive}):
    physicalRimResidualGraph ((Function.Embedding.subtype (·∈survive)).trans φ) covered =
      (physicalRimResidualGraph φ ∅\Del)\
        physicalRimCoveredGraph ((Function.Embedding.subtype (·∈survive)).trans φ) covered:=by
  ext x y
  simp only [SimpleGraph.sdiff_adj]
  constructor
  · rintro ⟨hxy,w,hw,he⟩
    have he':φ w.val=Sum.inl s(x,y):=he
    refine ⟨⟨⟨hxy,w.val,by simp,he'⟩,(hSurvive w.val x y he').mp w.property⟩,?_⟩
    rintro ⟨_,v,hv,hvphi⟩
    have heq:w=v:=by
      apply Subtype.ext
      apply φ.injective
      exact he'.trans hvphi.symm
    exact hw (heq ▸ hv)
  · rintro ⟨⟨⟨hxy,w,_,he⟩,hDel⟩,hUsed⟩
    have hw:w∈survive:=(hSurvive w x y he).mpr hDel
    let z:{w // w∈survive}:=⟨w,hw⟩
    refine ⟨hxy,z,?_,he⟩
    intro hz
    exact hUsed ⟨hxy,z,hz,he⟩
end Oberwolfach
