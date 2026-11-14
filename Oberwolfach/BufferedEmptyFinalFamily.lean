module

public import Oberwolfach.BufferedPathInteriorCompletion
public import Oberwolfach.PartialFactorWalkEdgeDisjointnessPoly

@[expose] public section
/-! If a factor has no final marked starts, its buffered complement is its
whole unreserved source. The resulting full source embeddings preserve their
physical edge sets and cross-factor disjointness. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem buffered_empty_final_family_completion
    {U Y:Type*} {X I:U→Type*} [∀u,Fintype (X u)] [∀u,DecidableEq (X u)] [∀u,Fintype (I u)]
    (hempty:∀u,IsEmpty (I u)) (G:∀u,SimpleGraph (X u)) (H:SimpleGraph Y)
    (n:∀u,I u→ℕ) (inner:∀u (i:I u),Fin (n u i+1)↪X u)
    (fC:∀u,{x // x∉bufferedPathStrictInterior (n u) (inner u)}↪Y)
    (hC:∀u x y (hx:x∉bufferedPathStrictInterior (n u) (inner u)) (hy:y∉bufferedPathStrictInterior (n u) (inner u)),
      (G u).Adj x y→H.Adj (fC u ⟨x,hx⟩) (fC u ⟨y,hy⟩))
    (hCC:∀u v,u≠v→Disjoint
      (partialFactorPhysicalEdgesPoly {x // x∉bufferedPathStrictInterior (n u) (inner u)}
        ((G u).induce {x | x∉bufferedPathStrictInterior (n u) (inner u)}) (fC u))
      (partialFactorPhysicalEdgesPoly {x // x∉bufferedPathStrictInterior (n v) (inner v)}
        ((G v).induce {x | x∉bufferedPathStrictInterior (n v) (inner v)}) (fC v))):
    ∃f:∀u,X u↪Y,
      (∀u x (hx:x∉bufferedPathStrictInterior (n u) (inner u)),f u x=fC u ⟨x,hx⟩) ∧
      (∀u x y,(G u).Adj x y→H.Adj (f u x) (f u y)) ∧
      (∀u,partialFactorPhysicalEdgesPoly (X u) (G u) (f u)=
        partialFactorPhysicalEdgesPoly {x // x∉bufferedPathStrictInterior (n u) (inner u)}
          ((G u).induce {x | x∉bufferedPathStrictInterior (n u) (inner u)}) (fC u)) ∧
      (∀u v,u≠v→Disjoint (partialFactorPhysicalEdgesPoly (X u) (G u) (f u))
        (partialFactorPhysicalEdgesPoly (X v) (G v) (f v))):=by
  have hnone:∀u x,x∉bufferedPathStrictInterior (n u) (inner u):=by
    intro u x hx
    obtain ⟨i,_,_⟩:=Finset.mem_biUnion.mp hx
    exact (hempty u).false i
  let f:∀u,X u↪Y:=fun u=>⟨fun x=>fC u ⟨x,hnone u x⟩,by
    intro x y hxy
    exact congrArg Subtype.val ((fC u).injective hxy)⟩
  have hf:∀u x (hx:x∉bufferedPathStrictInterior (n u) (inner u)),f u x=fC u ⟨x,hx⟩:=by
    intro u x hx
    rfl
  have hedge:∀u,partialFactorPhysicalEdgesPoly (X u) (G u) (f u)=
      partialFactorPhysicalEdgesPoly {x // x∉bufferedPathStrictInterior (n u) (inner u)}
        ((G u).induce {x | x∉bufferedPathStrictInterior (n u) (inner u)}) (fC u):=by
    intro u
    ext e
    constructor
    · rintro ⟨x,y,hxy,rfl⟩
      exact ⟨⟨x,hnone u x⟩,⟨y,hnone u y⟩,hxy,rfl⟩
    · rintro ⟨x,y,hxy,rfl⟩
      exact ⟨x.val,y.val,hxy,rfl⟩
  refine ⟨f,hf,?_,hedge,?_⟩
  · intro u x y hxy
    exact hC u x y (hnone u x) (hnone u y) hxy
  · intro u v huv
    rw [hedge u,hedge v]
    exact hCC u v huv
end Oberwolfach
