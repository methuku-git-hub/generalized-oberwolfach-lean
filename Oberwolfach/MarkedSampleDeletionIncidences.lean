module

public import Oberwolfach.MarkedSampleDeletedArcs
public import Oberwolfach.MarkedFiniteHostLocalBalances
public import Oberwolfach.MarkedNeighbourhoodPhysicalDeletion

@[expose] public section

/-! Exact occurrence counts in the physically deleted sample. The new
arc subtypes embed into the original ones and enumerate precisely the
surviving physical coordinates. This transfers actual finite balances. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 24000000
set_option maxRecDepth 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def markedSampleDeletedArcsEmbedding
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color) (D:Finset (Sym2 V)):
    (MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims σ D (Sum.inl e)) false⊕
      MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims σ D (Sum.inl e)) true)↪
    (MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false⊕
      MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true):=
  ((markedSampleDeletedArcEquiv P π d σ D false).toEmbedding.trans
    (Function.Embedding.subtype _)).sumMap
    ((markedSampleDeletedArcEquiv P π d σ D true).toEmbedding.trans
      (Function.Embedding.subtype _))

theorem markedSampleDeletedArcsEmbedding_range
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color) (D:Finset (Sym2 V)):
    Finset.univ.image (markedSampleDeletedArcsEmbedding P π d σ D)=
      Finset.univ.filter (fun a=>Sum.elim (fun e=>s(e.val.1,e.val.2)) (fun e=>s(e.val.1,π e.val.2)) a∉D):=by
  ext a
  simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_filter]
  constructor
  · rintro ⟨a,rfl⟩
    cases a with
    | inl a=>exact ((markedPhysicalRim_delete_iff P π d σ D false _ _).mp a.property).2
    | inr a=>exact ((markedPhysicalRim_delete_iff P π d σ D true _ _).mp a.property).2
  · intro ha
    cases a with
    | inl a=>
      refine ⟨Sum.inl ⟨a.val,(markedPhysicalRim_delete_iff P π d σ D false _ _).mpr ⟨a.property,ha⟩⟩,?_⟩
      rfl
    | inr a=>
      refine ⟨Sum.inr ⟨a.val,(markedPhysicalRim_delete_iff P π d σ D true _ _).mpr ⟨a.property,ha⟩⟩,?_⟩
      rfl

theorem markedSampleDeletedArcsEmbedding_filter_card
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color) (D:Finset (Sym2 V))
    (p:(MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false⊕
      MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true)→Prop):
    (Finset.univ.filter (fun a=>p (markedSampleDeletedArcsEmbedding P π d σ D a))).card=
      ((Finset.univ.filter (fun a=>Sum.elim (fun e=>s(e.val.1,e.val.2)) (fun e=>s(e.val.1,π e.val.2)) a∉D)).filter p).card:=by
  rw [←markedSampleDeletedArcsEmbedding_range,Finset.filter_image,
    Finset.card_image_of_injective _ (markedSampleDeletedArcsEmbedding P π d σ D).injective]

theorem markedSampleDeletedArcsEmbedding_endpoints_type
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color) (D:Finset (Sym2 V))
    (a:MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims σ D (Sum.inl e)) false⊕
      MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims σ D (Sum.inl e)) true):
    Sum.elim (fun e=>e.val.1) (fun e=>e.val.1) (markedSampleDeletedArcsEmbedding P π d σ D a)=
      Sum.elim (fun e=>e.val.1) (fun e=>e.val.1) a ∧
    Sum.elim (fun e=>e.val.2) (fun e=>e.val.2) (markedSampleDeletedArcsEmbedding P π d σ D a)=
      Sum.elim (fun e=>e.val.2) (fun e=>e.val.2) a ∧
    markedArcType (markedSampleDeletedArcsEmbedding P π d σ D a)=markedArcType a:=by
  cases a <;> exact ⟨rfl,rfl,rfl⟩

end Oberwolfach
