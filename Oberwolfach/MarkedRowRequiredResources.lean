module

public import Oberwolfach.MarkedRowCoverPackings

@[expose] public section

/-! The exact resources prescribed at a row: the supplied incoming and
outgoing physical rim edges, and the two types of root spokes. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T A X : Type} [DecidableEq V] [DecidableEq U] [Fintype A] [Fintype X]
    {tail head : E→V} {ktail khead : T→V} {π : Equiv.Perm V}

def markedRowRequiredResources (incoming : A→E⊕T) (outgoing : X→E⊕T)
    (v : V) (Y : Finset U) : Finset (Finset V⊕(V×U)) :=
  (Finset.univ.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π (incoming a)))∪
   Finset.univ.image (fun x=>Sum.inl (markedPhysicalEdge tail head ktail khead π (outgoing x))))∪
    Y.image (fun u=>Sum.inr (v,u))

theorem marked_row_required_covered {I : Type} (incoming : A→E⊕T) (outgoing : X→E⊕T)
    (v : V) (Y : Finset U) (C : I→Finset (Finset V⊕(V×U)))
    (hA : ∀ a,∃ i,Sum.inl (markedPhysicalEdge tail head ktail khead π (incoming a))∈C i)
    (hX : ∀ x,∃ i,Sum.inl (markedPhysicalEdge tail head ktail khead π (outgoing x))∈C i)
    (hY : ∀ u∈Y,∃ i,Sum.inr (v,u)∈C i) :
    ∀ e∈markedRowRequiredResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
      (π:=π) incoming outgoing v Y,∃ i,e∈C i := by
  intro e he
  rcases Finset.mem_union.mp he with he|he
  · rcases Finset.mem_union.mp he with he|he
    · obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp he
      exact hA a
    · obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp he
      exact hX x
  · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp he
    exact hY u hu

end Oberwolfach
