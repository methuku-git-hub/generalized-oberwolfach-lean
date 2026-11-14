module

public import Oberwolfach.MarkedEndpointArcEmbeddings

@[expose] public section

/-! The endpoint embeddings enumerate every sampled arc at the prescribed
root whose other auxiliary endpoint lies in the specified domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

theorem marked_endpoint_arc_embedding_exhaustive
    (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ) (A : Finset V)
    (mark incoming : Bool) (x : V) (σ : RawMarkedOutcome V U Γ Color)
    (e : MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) mark)
    (hroot : (if incoming then e.val.2 else e.val.1)=x)
    (hother : (if incoming then e.val.1 else e.val.2)∈A) :
    ∃ z,markedEndpointArcEmbedding P π d A mark incoming x σ z=e := by
  let y := if incoming then e.val.1 else e.val.2
  have hpair : (if incoming then y else x,if incoming then x else y)=e.val := by
    cases incoming <;> apply Prod.ext <;> first | exact hroot.symm | rfl
  have hy : y∈markedEndpointLabels P π d A (mark,incoming,x) σ := by
    rw [marked_endpoint_labels_actual]
    apply Finset.mem_filter.mpr
    refine ⟨hother,?_⟩
    have hh := congrArg (fun a:V×V=>markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark a.1 a.2) hpair
    exact hh.trans e.property
  refine ⟨⟨y,hy⟩,Subtype.ext hpair⟩

theorem marked_endpoint_tagged_arc_embedding_exhaustive
    (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ) (A : Finset V)
    (incoming : Bool) (x : V) (σ : RawMarkedOutcome V U Γ Color)
    (e : (MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false)⊕
      (MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true))
    (hroot : (if incoming then Sum.elim (fun e=>e.val.2) (fun e=>e.val.2) e
      else Sum.elim (fun e=>e.val.1) (fun e=>e.val.1) e)=x)
    (hother : (if incoming then Sum.elim (fun e=>e.val.1) (fun e=>e.val.1) e
      else Sum.elim (fun e=>e.val.2) (fun e=>e.val.2) e)∈A) :
    ∃ z,markedEndpointTaggedArcEmbedding P π d A incoming x σ z=e := by
  cases e with
  | inl e=>
    obtain ⟨z,hz⟩ := marked_endpoint_arc_embedding_exhaustive P π d A false incoming x σ e hroot hother
    exact ⟨Sum.inl z,congrArg Sum.inl hz⟩
  | inr e=>
    obtain ⟨z,hz⟩ := marked_endpoint_arc_embedding_exhaustive P π d A true incoming x σ e hroot hother
    exact ⟨Sum.inr z,congrArg Sum.inr hz⟩

end Oberwolfach
