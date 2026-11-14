module

public import Oberwolfach.BufferedFactorFamilyCompletion
public import Oberwolfach.InteriorImageSeparation

@[expose] public section
/-! Discharge interior/complement image separation using endpoint agreement
and the displayed reserved-target avoidance. -/
set_option autoImplicit false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem buffered_factor_family_completion_from_reserved_avoidance
    {U X Y:Type*} [Fintype X] [DecidableEq X]
    (I:U→Type*) [∀u,Fintype (I u)]
    (G:U→SimpleGraph X) (H:SimpleGraph Y) (hG:∀u,(G u).IsRegularOfDegree 2)
    (n:∀u,I u→ℕ)
    (ext:∀u (i:I u),Fin (n u i+5)↪X) (inner:∀u (i:I u),Fin (n u i+1)↪X)
    (hinner:∀u i p,inner u i p=ext u i ⟨p.val+2,by omega⟩)
    (hwalk:∀u i,∃p:(G u).Walk (ext u i ⟨0,by omega⟩) (ext u i ⟨n u i+4,by omega⟩),
      p.length=n u i+4 ∧ p.support=List.ofFn (ext u i))
    (fA:∀u,{x // x∈bufferedPathFullDomain (n u) (inner u)}↪Y)
    (fC:∀u,{x // x∉bufferedPathStrictInterior (n u) (inner u)}↪Y)
    (hA:∀u x y (hx:x∈bufferedPathFullDomain (n u) (inner u)) (hy:y∈bufferedPathFullDomain (n u) (inner u)),
      (G u).Adj x y→H.Adj (fA u ⟨x,hx⟩) (fA u ⟨y,hy⟩))
    (hC:∀u x y (hx:x∉bufferedPathStrictInterior (n u) (inner u)) (hy:y∉bufferedPathStrictInterior (n u) (inner u)),
      (G u).Adj x y→H.Adj (fC u ⟨x,hx⟩) (fC u ⟨y,hy⟩))
    (hend:∀u i (p:Fin (n u i+1)),(p=0 ∨ p=Fin.last (n u i))→
      ∀ hpD:inner u i p∉bufferedPathStrictInterior (n u) (inner u),
      fA u ⟨inner u i p,buffered_path_vertex_mem_domain (n u) (inner u) i p⟩=fC u ⟨inner u i p,hpD⟩)
    (R:U→Finset Y)
    (hinside:∀u x (hx:x∈bufferedPathStrictInterior (n u) (inner u)),
      fA u ⟨x,buffered_strict_interior_subset_domain (n u) (inner u) hx⟩∈R u)
    (havoid:∀u x (hx:x∉bufferedPathStrictInterior (n u) (inner u)),
      x∉bufferedPathFullDomain (n u) (inner u)→fC u ⟨x,hx⟩∉R u)
    (hAA:∀u v,u≠v→Disjoint
      (partialFactorPhysicalEdgesPoly {x // x∈bufferedPathFullDomain (n u) (inner u)}
        ((G u).induce (↑(bufferedPathFullDomain (n u) (inner u)):Set X)) (fA u))
      (partialFactorPhysicalEdgesPoly {x // x∈bufferedPathFullDomain (n v) (inner v)}
        ((G v).induce (↑(bufferedPathFullDomain (n v) (inner v)):Set X)) (fA v)))
    (hAC:∀u v,u≠v→Disjoint
      (partialFactorPhysicalEdgesPoly {x // x∈bufferedPathFullDomain (n u) (inner u)}
        ((G u).induce (↑(bufferedPathFullDomain (n u) (inner u)):Set X)) (fA u))
      (partialFactorPhysicalEdgesPoly {x // x∉bufferedPathStrictInterior (n v) (inner v)}
        ((G v).induce {x | x∉bufferedPathStrictInterior (n v) (inner v)}) (fC v)))
    (hCC:∀u v,u≠v→Disjoint
      (partialFactorPhysicalEdgesPoly {x // x∉bufferedPathStrictInterior (n u) (inner u)}
        ((G u).induce {x | x∉bufferedPathStrictInterior (n u) (inner u)}) (fC u))
      (partialFactorPhysicalEdgesPoly {x // x∉bufferedPathStrictInterior (n v) (inner v)}
        ((G v).induce {x | x∉bufferedPathStrictInterior (n v) (inner v)}) (fC v))) :
    ∃f:∀u,X↪Y,
      (∀u x (hx:x∈bufferedPathFullDomain (n u) (inner u)),f u x=fA u ⟨x,hx⟩) ∧
      (∀u x (hx:x∉bufferedPathStrictInterior (n u) (inner u)),f u x=fC u ⟨x,hx⟩) ∧
      (∀u x y,(G u).Adj x y→H.Adj (f u x) (f u y)) ∧
      (∀u v,u≠v→Disjoint (partialFactorPhysicalEdgesPoly X (G u) (f u))
        (partialFactorPhysicalEdgesPoly X (G v) (f v))) := by
  have hbound:∀u x (hx:x∈bufferedPathFullDomain (n u) (inner u))
      (hxD:x∉bufferedPathStrictInterior (n u) (inner u)),fA u ⟨x,hx⟩=fC u ⟨x,hxD⟩:=by
    intro u x hx hxD
    obtain ⟨i,hi|hi⟩:=buffered_path_boundary_is_endpoint (n u) (inner u) x hx hxD
    · subst x
      exact hend u i 0 (Or.inl rfl) hxD
    · subst x
      exact hend u i (Fin.last (n u i)) (Or.inr rfl) hxD
  have hdis:∀u x (hx:x∈bufferedPathStrictInterior (n u) (inner u))
      y (hy:y∉bufferedPathStrictInterior (n u) (inner u)),
      fA u ⟨x,buffered_strict_interior_subset_domain (n u) (inner u) hx⟩≠fC u ⟨y,hy⟩:=by
    intro u
    exact interior_image_separated_by_boundary_and_avoidance
      (bufferedPathFullDomain (n u) (inner u)) (bufferedPathStrictInterior (n u) (inner u))
      (buffered_strict_interior_subset_domain (n u) (inner u)) (R u) (fA u) (fC u)
      (hbound u) (hinside u) (havoid u)
  exact buffered_factor_family_completion I G H hG n ext inner hinner hwalk fA fC hA hC hend hdis hAA hAC hCC
end Oberwolfach
