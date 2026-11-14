module

public import Oberwolfach.MarkedSpokeDeletionRepresentation

@[expose] public section
/-! The typewise intersection with a later host is an actual deletion of
the original spoke sample, even if the later host also has added pairs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem marked_spoke_common_subhost_deletion
    (H H':Bool→V→U→Prop) (I:Finset V) (J:Finset U)
    (htypes:∀ v u,¬(H false v u∧H true v u))
    (hinner:∀ b v u,v∈I→u∈J→(H b v u↔H' b v u)):
    ∃ D:SimpleGraph (V⊕U),
      (∀ b v u,markedDeletePhysicalSpokes H D b v u↔H b v u∧H' b v u) ∧
      (∀ v∈I,∀ u∈J,¬D.Adj (Sum.inl v) (Sum.inr u)) ∧
      (∀ v,D.degree (Sum.inl v)=(Finset.univ.filter (fun u=>∃ b,H b v u∧¬H' b v u)).card) ∧
      (∀ u,D.degree (Sum.inr u)=(Finset.univ.filter (fun v=>∃ b,H b v u∧¬H' b v u)).card) :=by
  let S:Finset (V×U):=Finset.univ.filter (fun z=>∃ b,H b z.1 z.2∧¬H' b z.1 z.2)
  let D:=markedFiniteSpokeGraph S
  refine ⟨D,?_,?_,?_,?_⟩
  · intro b v u
    simp only [markedDeletePhysicalSpokes,D,markedFiniteSpokeGraph_adj,S,Finset.mem_filter,Finset.mem_univ,true_and]
    have ht:=htypes v u
    cases b <;> simp only [Bool.exists_bool] <;> tauto
  · intro v hv u hu
    simp only [D,markedFiniteSpokeGraph_adj,S,Finset.mem_filter,Finset.mem_univ,true_and]
    rintro ⟨b,hb,hnot⟩
    exact hnot ((hinner b v u hv hu).mp hb)
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
