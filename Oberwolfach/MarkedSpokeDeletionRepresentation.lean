module

public import Oberwolfach.MarkedFiniteDeletionDegrees
public import Oberwolfach.MarkedNeighbourhoodPhysicalDeletion

@[expose] public section

/-! A typed spoke subhost of a type-disjoint original host is obtained by
one physical spoke deletion. Its row and column degrees count the deleted
physical pairs exactly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem marked_spoke_deletion_representation
    (H H':Bool→V→U→Prop)
    (hsub:∀ b v u,H' b v u→H b v u)
    (htypes:∀ v u,¬(H false v u∧H true v u)):
    ∃ D:SimpleGraph (V⊕U),
      H'=markedDeletePhysicalSpokes H D ∧
      (∀ v,D.degree (Sum.inl v)=(Finset.univ.filter (fun u=>∃ b,H b v u∧¬H' b v u)).card) ∧
      (∀ u,D.degree (Sum.inr u)=(Finset.univ.filter (fun v=>∃ b,H b v u∧¬H' b v u)).card) := by
  let S:Finset (V×U):=Finset.univ.filter (fun z=>∃ b,H b z.1 z.2∧¬H' b z.1 z.2)
  let D:=markedFiniteSpokeGraph S
  refine ⟨D,?_,?_,?_⟩
  · funext b v u
    apply propext
    simp only [markedDeletePhysicalSpokes,D,markedFiniteSpokeGraph_adj,S,Finset.mem_filter,Finset.mem_univ,true_and]
    have hs0:=hsub false v u
    have hs1:=hsub true v u
    have ht:=htypes v u
    cases b <;> simp only [Bool.exists_bool] <;> tauto
  · intro v
    change (markedFiniteSpokeGraph S).degree (Sum.inl v)=_
    rw [markedFiniteSpokeGraph_degree_row]
    congr 1
    ext u
    simp [S]
  · intro u
    change (markedFiniteSpokeGraph S).degree (Sum.inr u)=_
    rw [markedFiniteSpokeGraph_degree_col]
    congr 1
    ext v
    simp [S]
end Oberwolfach
