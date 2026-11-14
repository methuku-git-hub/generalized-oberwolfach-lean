module

public import Oberwolfach.FiniteComplementPartitionCard

@[expose] public section
/-! Record the two equalities of the marked interval vertex-count identity. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_interval_partition_count
    {V J:Type*} [Fintype V] [DecidableEq V] [Fintype J]
    (S Y:Finset V) (c:ℕ) (endpoints:J→V)
    (hcount:S.card=c*Y.card) (hend:∀j,endpoints j∉S):
    S.card=c*Y.card ∧
      S.card=Fintype.card V-(Finset.univ\(S∪Finset.univ.image endpoints)).card-
        (Finset.univ.image endpoints).card := by
  have hdis:Disjoint S (Finset.univ.image endpoints):=by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hy
    exact hend j hx
  exact ⟨hcount,finite_complement_partition_card S (Finset.univ.image endpoints) hdis⟩
end Oberwolfach
