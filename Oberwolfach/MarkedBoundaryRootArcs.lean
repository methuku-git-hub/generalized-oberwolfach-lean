module

public import Oberwolfach.MarkedAssignedArcDisjointness

@[expose] public section

/-! Distinct actual boundary arcs have disjoint prescribed physical rims,
including when the outside roots differ. An outgoing arc cannot equal an
incoming arc because its tail is outside the free row set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V E K:Type} [DecidableEq V]

theorem marked_assigned_boundary_root_rims_disjoint {I : Type}
    (tail head : E → V) (ktail khead : K → V) (π : Equiv.Perm V)
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (X : Finset V) (v : I→V) (incoming outgoing : I → E⊕K)
    (hi : Function.Injective incoming) (ho : Function.Injective outgoing)
    (hhead : ∀ i, Sum.elim head khead (incoming i)=v i)
    (htail : ∀ i, Sum.elim tail ktail (outgoing i)=v i)
    (hv : ∀ i,v i∉X) (hinX : ∀ i,Sum.elim tail ktail (incoming i)∈X) :
    ∀ i j, i≠j → Disjoint
      (markedRowRootRims π (v i) (Sum.elim head khead (outgoing i)) (Sum.elim tail ktail (incoming i))
        (incoming i).isRight (outgoing i).isRight)
      (markedRowRootRims π (v j) (Sum.elim head khead (outgoing j)) (Sum.elim tail ktail (incoming j))
        (incoming j).isRight (outgoing j).isRight) := by
  have he (i : I) : markedRowRootRims π (v i)
      (Sum.elim head khead (outgoing i)) (Sum.elim tail ktail (incoming i))
      (incoming i).isRight (outgoing i).isRight=
      {markedPhysicalEdge tail head ktail khead π (outgoing i),markedPhysicalEdge tail head ktail khead π (incoming i)} := by
    simp only [markedRowRootRims,markedPhysicalEdge_typed_formula,hhead,htail]
  have hcross (i j : I) : outgoing i≠incoming j := by
    intro h
    have he:Sum.elim tail ktail (incoming j)=v i:=(congrArg (Sum.elim tail ktail) h).symm.trans (htail i)
    exact hv i (he ▸ hinX j)
  intro i j hij
  rw [he,he]
  apply Finset.disjoint_left.mpr
  intro e hei hej
  have hei' : e=markedPhysicalEdge tail head ktail khead π (outgoing i) ∨
      e=markedPhysicalEdge tail head ktail khead π (incoming i) := by simpa using hei
  have hej' : e=markedPhysicalEdge tail head ktail khead π (outgoing j) ∨
      e=markedPhysicalEdge tail head ktail khead π (incoming j) := by simpa using hej
  rcases hei' with hei|hei <;> rcases hej' with hej|hej
  · exact hij (ho (hp (hei.symm.trans hej)))
  · exact hcross i j (hp (hei.symm.trans hej))
  · exact hcross j i (hp (hej.symm.trans hei))
  · exact hij (hi (hp (hei.symm.trans hej)))

end Oberwolfach
