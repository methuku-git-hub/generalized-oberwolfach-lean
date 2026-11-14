module

public import Oberwolfach.PhysicalRimResourceResidual

@[expose] public section
/-! The physical residual of an embedded surviving resource type is the
original rim graph with the deleted and covered edges removed. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem physical_rim_surviving_embedding_eq
    {V U W Z:Type} [Fintype V] [Fintype U] [Fintype W] [Fintype Z]
    [DecidableEq V] [DecidableEq U] [DecidableEq W] [DecidableEq Z]
    (φ:W↪Sym2 V⊕(V×U)) (f:Z↪W) (Del:SimpleGraph V)
    (hSurvive:∀w x y,φ w=Sum.inl s(x,y)→((∃z,f z=w)↔¬Del.Adj x y))
    (covered:Finset Z):
    physicalRimResidualGraph (f.trans φ) covered =
      (physicalRimResidualGraph φ ∅\Del)\physicalRimCoveredGraph (f.trans φ) covered:=by
  ext x y
  simp only [SimpleGraph.sdiff_adj]
  constructor
  · rintro ⟨hxy,w,hw,he⟩
    have he':φ (f w)=Sum.inl s(x,y):=he
    refine ⟨⟨⟨hxy,f w,by simp,he'⟩,(hSurvive (f w) x y he').mp ⟨w,rfl⟩⟩,?_⟩
    rintro ⟨_,v,hv,hvphi⟩
    have heq:w=v:=by
      apply f.injective
      apply φ.injective
      exact he'.trans hvphi.symm
    exact hw (heq ▸ hv)
  · rintro ⟨⟨⟨hxy,w,_,he⟩,hDel⟩,hUsed⟩
    obtain ⟨z,hz⟩:=(hSurvive w x y he).mpr hDel
    refine ⟨hxy,z,?_,?_⟩
    · intro hc
      apply hUsed
      refine ⟨hxy,z,hc,?_⟩
      change φ (f z)=Sum.inl s(x,y)
      rw [hz]
      exact he
    · change φ (f z)=Sum.inl s(x,y)
      rw [hz]
      exact he
end Oberwolfach
