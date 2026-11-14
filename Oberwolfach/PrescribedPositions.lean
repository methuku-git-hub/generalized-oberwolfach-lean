module

public import Oberwolfach.PrescribedPositionsLists
public import Oberwolfach.PrescribedTargetMatching

@[expose] public section
/-! Prescribe the physical endpoints of an oriented matching and a disjoint
set of isolated labels in a degree-two source graph. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X V:Type} [Fintype X] [Fintype V] [DecidableEq X] [DecidableEq V]

theorem prescribed_positions (Q:SimpleGraph X) (D:X→X→Prop)
    (hdeg:∀x,Q.degree x≤2) (hrep:∀x y,Q.Adj x y→D x y ∨ D y x)
    (hDQ:∀x y,D x y→Q.Adj x y) (horiented:∀x y,D x y→¬D y x)
    (A:Finset X) (hA:∀x∈A,∀y∈A,¬Q.Adj x y) (f:X→V) (hinj:Set.InjOn f (↑A:Set X))
    (M:Finset (V×V)) (hM:IsPrescribedOrientedMatching M) (Z:Finset V)
    (hOldM:Disjoint (A.image f) (prescribedMatchingEndpoints M))
    (hOldZ:Disjoint (A.image f) Z) (hMZ:Disjoint (prescribedMatchingEndpoints M) Z)
    (hedges:Fintype.card X≤Q.edgeFinset.card+A.card)
    (hsize:8*A.card+8*M.card+4*Z.card+10≤Fintype.card X):
    ∃ (B:Finset X) (g:X→V),A⊆B ∧ Set.InjOn g (↑B:Set X) ∧ (∀x∈A,g x=f x) ∧
      B.image g=A.image f∪prescribedMatchingEndpoints M∪Z ∧
      (prescribedInducedArcs D B).image (Prod.map g g)=M := by
  let ms:=M.toList
  let zs:=Z.toList
  have hmn:(ms.flatMap prescribedPairVertices).Nodup:=prescribed_target_matching_list_nodup M hM
  have hzn:zs.Nodup:=Finset.nodup_toList Z
  have hend:(ms.flatMap prescribedPairVertices).toFinset=prescribedMatchingEndpoints M:=
    prescribed_target_matching_list_endpoints M
  have hz:zs.toFinset=Z:=by simp [zs]
  have hmz:List.Disjoint (ms.flatMap prescribedPairVertices) zs:=by
    apply List.disjoint_left.mpr
    intro x hx hy
    apply (Finset.disjoint_left.mp hMZ)
    · rw [←hend];exact List.mem_toFinset.mpr hx
    · rw [←hz];exact List.mem_toFinset.mpr hy
  have hold:Disjoint (A.image f) (ms.flatMap prescribedPairVertices++zs).toFinset:=by
    rw [List.toFinset_append,hend,hz]
    exact Finset.disjoint_union_right.mpr ⟨hOldM,hOldZ⟩
  have hsize':8*A.card+8*ms.length+4*zs.length+10≤Fintype.card X:=by simpa [ms,zs] using hsize
  obtain ⟨B,g,hAB,hginj,hgpres,himage,harcs⟩:=prescribed_positions_from_lists Q D hdeg hrep hDQ horiented
    A hA f hinj ms zs hmn hzn hmz hold hedges hsize'
  refine ⟨B,g,hAB,hginj,hgpres,?_,?_⟩
  · simpa [hend,hz] using himage
  · simpa [ms] using harcs
end Oberwolfach
