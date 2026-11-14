module

public import Oberwolfach.MarkedEndpointArcExhaustion
public import Oberwolfach.MarkedSampleDeletionIncidences

@[expose] public section

/-! The actual endpoint lists after a physical rim deletion embed into the
original typed host. They enumerate exactly its surviving incident arcs;
their directions, types and original occurrence identifiers are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Gamma Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Gamma] [Fintype Color]

def markedDeletedEndpointArcEmbedding
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (X:Finset V) (incoming:Bool) (x:V)
    (σ:RawMarkedOutcome V U Gamma Color) (D:Finset (Sym2 V)):
    (markedEndpointLabels P π d X (false,incoming,x) (rawMarkedDeleteRims σ D))⊕
      (markedEndpointLabels P π d X (true,incoming,x) (rawMarkedDeleteRims σ D))↪
    (MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false)⊕
      (MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true):=
  (markedEndpointTaggedArcEmbedding P π d X incoming x (rawMarkedDeleteRims σ D)).trans
    (markedSampleDeletedArcsEmbedding P π d σ D)

theorem marked_deleted_endpoint_embedding_endpoints_type
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (X:Finset V) (incoming:Bool) (x:V)
    (σ:RawMarkedOutcome V U Gamma Color) (D:Finset (Sym2 V))
    (z:(markedEndpointLabels P π d X (false,incoming,x) (rawMarkedDeleteRims σ D))⊕
      (markedEndpointLabels P π d X (true,incoming,x) (rawMarkedDeleteRims σ D))):
    let a:=markedDeletedEndpointArcEmbedding P π d X incoming x σ D z;
    Sum.elim (fun e=>e.val.1) (fun e=>e.val.1) a=
      (if incoming then Sum.elim Subtype.val Subtype.val z else x)∧
    Sum.elim (fun e=>e.val.2) (fun e=>e.val.2) a=
      (if incoming then x else Sum.elim Subtype.val Subtype.val z)∧a.isRight=z.isRight:=by
  cases z <;> exact ⟨rfl,rfl,rfl⟩

theorem marked_deleted_endpoint_embedding_survives
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (X:Finset V) (incoming:Bool) (x:V)
    (σ:RawMarkedOutcome V U Gamma Color) (D:Finset (Sym2 V))
    (z:(markedEndpointLabels P π d X (false,incoming,x) (rawMarkedDeleteRims σ D))⊕
      (markedEndpointLabels P π d X (true,incoming,x) (rawMarkedDeleteRims σ D))):
    Sum.elim (fun e=>s(e.val.1,e.val.2)) (fun e=>s(e.val.1,π e.val.2))
      (markedDeletedEndpointArcEmbedding P π d X incoming x σ D z)∉D:=by
  have hm:markedDeletedEndpointArcEmbedding P π d X incoming x σ D z∈
      Finset.univ.image (markedSampleDeletedArcsEmbedding P π d σ D):=
    Finset.mem_image.mpr ⟨markedEndpointTaggedArcEmbedding P π d X incoming x (rawMarkedDeleteRims σ D) z,
      Finset.mem_univ _,rfl⟩
  rw [markedSampleDeletedArcsEmbedding_range] at hm
  exact (Finset.mem_filter.mp hm).2

theorem marked_deleted_endpoint_embedding_exhaustive
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (X:Finset V) (incoming:Bool) (x:V)
    (σ:RawMarkedOutcome V U Gamma Color) (D:Finset (Sym2 V))
    (a:(MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false)⊕
      (MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true))
    (ha:Sum.elim (fun e=>s(e.val.1,e.val.2)) (fun e=>s(e.val.1,π e.val.2)) a∉D)
    (hroot:(if incoming then Sum.elim (fun e=>e.val.2) (fun e=>e.val.2) a
      else Sum.elim (fun e=>e.val.1) (fun e=>e.val.1) a)=x)
    (hother:(if incoming then Sum.elim (fun e=>e.val.1) (fun e=>e.val.1) a
      else Sum.elim (fun e=>e.val.2) (fun e=>e.val.2) a)∈X):
    ∃ z,markedDeletedEndpointArcEmbedding P π d X incoming x σ D z=a:=by
  have hm:a∈Finset.univ.image (markedSampleDeletedArcsEmbedding P π d σ D):=by
    rw [markedSampleDeletedArcsEmbedding_range]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩
  obtain ⟨a',_,rfl⟩:=Finset.mem_image.mp hm
  have he:=markedSampleDeletedArcsEmbedding_endpoints_type P π d σ D a'
  rw [he.1,he.2.1] at hroot hother
  obtain ⟨z,hz⟩:=marked_endpoint_tagged_arc_embedding_exhaustive P π d X incoming x
    (rawMarkedDeleteRims σ D) a' hroot hother
  exact ⟨z,congrArg (markedSampleDeletedArcsEmbedding P π d σ D) hz⟩

end Oberwolfach
