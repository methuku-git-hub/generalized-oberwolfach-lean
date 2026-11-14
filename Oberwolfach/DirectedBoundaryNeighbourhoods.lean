module

public import Oberwolfach.DirectedBoundarySupportEvent

@[expose] public section

/-! Identify the constructed boundary support with the actual retained
incoming/outgoing neighbourhood, followed by its successor image. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A W E:Type*} [Fintype A] [Fintype W] [Fintype E]
  [DecidableEq A] [DecidableEq W] [DecidableEq E]

def directedBoundaryNeighbours (tail head:A→W) (coin:A→E) (X:Finset W)
    (σ:E→Bool) (x:W):Finset W :=
  X.filter (fun y=>∃ a,((tail a=x∧head a=y)∨(head a=x∧tail a=y))∧σ (coin a)=true)

theorem boundary_inside_image_eq_neighbours (tail head:A→W) (coin:A→E) (X:Finset W)
    (σ:E→Bool) (x:W) (hx:x∉X):
    (Finset.univ.filter (fun a:DirectedBoundaryEdge tail head X=>
      boundaryOutside tail head X a=x∧σ (coin a.val)=true)).image (boundaryInside tail head X)=
      directedBoundaryNeighbours tail head coin X σ x := by
  ext y
  constructor
  · intro hy
    obtain ⟨a,ha,hay⟩:=Finset.mem_image.mp hy
    have hao:boundaryOutside tail head X a=x:=(Finset.mem_filter.mp ha).2.1
    have hs:σ (coin a.val)=true:=(Finset.mem_filter.mp ha).2.2
    apply Finset.mem_filter.mpr
    refine ⟨hay ▸ boundaryInside_mem tail head X a,⟨a.val,?_,hs⟩⟩
    have he:=boundary_ordered_endpoints tail head X a
    rw [hao,hay] at he
    by_cases ht:tail a.val∈X
    · simp only [ht,ite_true] at he
      exact Or.inr ⟨he.2,he.1⟩
    · simp only [ht,ite_false] at he
      exact Or.inl he
  · intro hy
    obtain ⟨hy,⟨a,ha,hs⟩⟩:=Finset.mem_filter.mp hy
    rcases ha with ⟨ht,hh⟩|⟨hh,ht⟩
    · have hp:(tail a∉X∧head a∈X)∨(tail a∈X∧head a∉X):=Or.inl ⟨ht.symm ▸ hx,hh.symm ▸ hy⟩
      refine Finset.mem_image.mpr ⟨⟨a,hp⟩,?_,?_⟩
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _,by simp [boundaryOutside,ht,hx,hs]⟩
      · simp only [boundaryInside,ht,hx,ite_false,hh]
    · have hp:(tail a∉X∧head a∈X)∨(tail a∈X∧head a∉X):=Or.inr ⟨ht.symm ▸ hy,hh.symm ▸ hx⟩
      refine Finset.mem_image.mpr ⟨⟨a,hp⟩,?_,?_⟩
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _,by simp [boundaryOutside,ht,hy,hh,hs]⟩
      · simp only [boundaryInside,ht,hy,ite_true]

theorem directedBoundarySupport_eq_neighbours (tail head:A→W) (coin:A→E) (X:Finset W)
    (π:Equiv.Perm W) (σ:E→Bool) (x:W) (hx:x∉X):
    directedBoundarySupport tail head coin X π σ x=
      directedBoundaryNeighbours tail head coin X σ x∪
      (directedBoundaryNeighbours tail head coin X σ x).image π := by
  exact congrArg (fun Y:Finset W=>Y∪Y.image π)
    (boundary_inside_image_eq_neighbours tail head coin X σ x hx)

end Oberwolfach
