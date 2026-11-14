module

public import Oberwolfach.MarkedEndpointLabelIdentities

@[expose] public section

/-! An actual endpoint of a fixed type determines exactly one sampled
arc. The resulting embeddings preserve the direction and the marked tag. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

def markedEndpointArcEmbedding
    (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ) (A : Finset V)
    (mark incoming : Bool) (x : V) (σ : RawMarkedOutcome V U Γ Color) :
    markedEndpointLabels P π d A (mark,incoming,x) σ ↪
      MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) mark where
  toFun z := ⟨(if incoming then z.val else x,if incoming then x else z.val),by
    have hz := Eq.mp (congrArg (fun C : Finset V=>z.val∈C)
      (marked_endpoint_labels_actual P π d A mark incoming x σ)) z.property
    exact (Finset.mem_filter.mp hz).2⟩
  inj' := by
    intro z w he
    have heq := congrArg Subtype.val he
    apply Subtype.ext
    cases incoming
    · exact congrArg Prod.snd heq
    · exact congrArg Prod.fst heq

def markedEndpointTaggedArcEmbedding
    (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ) (A : Finset V)
    (incoming : Bool) (x : V) (σ : RawMarkedOutcome V U Γ Color) :
    (markedEndpointLabels P π d A (false,incoming,x) σ) ⊕
      (markedEndpointLabels P π d A (true,incoming,x) σ) ↪
    (MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false) ⊕
      (MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true) :=
  (markedEndpointArcEmbedding P π d A false incoming x σ).sumMap
    (markedEndpointArcEmbedding P π d A true incoming x σ)

theorem marked_endpoint_arc_embedding_tail
    (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ) (A : Finset V)
    (incoming : Bool) (x : V) (σ : RawMarkedOutcome V U Γ Color)
    (z : (markedEndpointLabels P π d A (false,incoming,x) σ) ⊕
      (markedEndpointLabels P π d A (true,incoming,x) σ)) :
    Sum.elim (fun e=>e.val.1) (fun e=>e.val.1) (markedEndpointTaggedArcEmbedding P π d A incoming x σ z)=
      if incoming then Sum.elim Subtype.val Subtype.val z else x := by
  cases z <;> rfl

theorem marked_endpoint_arc_embedding_head
    (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ) (A : Finset V)
    (incoming : Bool) (x : V) (σ : RawMarkedOutcome V U Γ Color)
    (z : (markedEndpointLabels P π d A (false,incoming,x) σ) ⊕
      (markedEndpointLabels P π d A (true,incoming,x) σ)) :
    Sum.elim (fun e=>e.val.2) (fun e=>e.val.2) (markedEndpointTaggedArcEmbedding P π d A incoming x σ z)=
      if incoming then x else Sum.elim Subtype.val Subtype.val z := by
  cases z <;> rfl

theorem marked_endpoint_arc_embedding_type
    (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ) (A : Finset V)
    (incoming : Bool) (x : V) (σ : RawMarkedOutcome V U Γ Color)
    (z : (markedEndpointLabels P π d A (false,incoming,x) σ) ⊕
      (markedEndpointLabels P π d A (true,incoming,x) σ)) :
    (markedEndpointTaggedArcEmbedding P π d A incoming x σ z).isRight=z.isRight := by
  cases z <;> rfl

theorem marked_endpoint_label_membership
    (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ) (A : Finset V)
    (incoming : Bool) (x : V) (σ : RawMarkedOutcome V U Γ Color)
    (z : (markedEndpointLabels P π d A (false,incoming,x) σ) ⊕
      (markedEndpointLabels P π d A (true,incoming,x) σ)) :
    Sum.elim Subtype.val Subtype.val z∈A ∧
      ¬PermutationClose π (3*d) (Sum.elim Subtype.val Subtype.val z) x := by
  cases z with
  | inl z=>
    refine ⟨(Finset.mem_filter.mp ((Finset.mem_filter.mp z.property).1)).1,?_⟩
    exact fun hc=>marked_endpoint_labels_separated P π d A (false,incoming,x) σ z.val z.property
      ((permutationClose_symm π (3*d) _ _).mp hc)
  | inr z=>
    refine ⟨(Finset.mem_filter.mp ((Finset.mem_filter.mp z.property).1)).1,?_⟩
    exact fun hc=>marked_endpoint_labels_separated P π d A (true,incoming,x) σ z.val z.property
      ((permutationClose_symm π (3*d) _ _).mp hc)

end Oberwolfach
