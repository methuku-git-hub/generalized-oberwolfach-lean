module

public import Oberwolfach.OrdinaryAttachmentWheels
public import Oberwolfach.OrdinaryExactDecomposition
public import Oberwolfach.OrdinaryTotalDivisibility

@[expose] public section

/-! A decomposable comparison graph with prescribed total edge counts.
It consists of disjoint wheels, with harmless unused private zero labels
retained to match the finite attachment representation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I W : Type} [Fintype I] [Fintype W] [DecidableEq I] [DecidableEq W]

abbrev disjointWheelSpokes (z : W) : (I⊕(I×W)) → (Empty⊕I) → Prop :=
  ordinaryAttachmentSpokes (fun (_ : I) (_ : Empty) => False) z id

def disjointWheelSpokeEquiv (z : W) :
    (I×W) ≃ {e:(I⊕(I×W))×(Empty⊕I) // disjointWheelSpokes z e.1 e.2} := by
  let f : (I×W) → {e:(I⊕(I×W))×(Empty⊕I) // disjointWheelSpokes z e.1 e.2} := fun p =>
    ⟨(attachmentWheelEmbedding z id p.1 p.2,.inr p.1),by
      by_cases h : p.2=z <;> simp [attachmentWheelEmbedding,disjointWheelSpokes,ordinaryAttachmentSpokes,h]⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨i,w⟩ ⟨j,w'⟩ he
    have hij : i=j := Sum.inr.inj (congrArg (fun a => a.val.2) he)
    subst j
    have hww : w=w' := (attachmentWheelEmbedding z id i).injective (congrArg (fun a => a.val.1) he)
    exact Prod.ext rfl hww
  · rintro ⟨⟨a,b⟩,h⟩
    cases b with
    | inl b => exact b.elim
    | inr i =>
      cases a with
      | inl a =>
        change i=a at h
        subst a
        refine ⟨(i,z),?_⟩
        apply Subtype.ext
        simp [f,attachmentWheelEmbedding]
      | inr p =>
        rcases p with ⟨j,w⟩
        change w≠z ∧ j=i at h
        obtain ⟨hw,hji⟩ := h
        subst j
        refine ⟨(i,w),?_⟩
        apply Subtype.ext
        simp [f,attachmentWheelEmbedding,hw]

theorem disjointWheelSpokes_card (z : W) :
    Fintype.card {e:(I⊕(I×W))×(Empty⊕I) // disjointWheelSpokes z e.1 e.2}=Fintype.card I*Fintype.card W := by
  rw [←Fintype.card_congr (disjointWheelSpokeEquiv (I:=I) z),Fintype.card_prod]

theorem disjoint_wheel_comparison (C : SimpleGraph W) (r : ℕ) (hC : IsEmbeddedCycle C r)
    (z : W) (hfull : ∀ w,w∈C.support) (hW : Fintype.card W=r) :
    let G := ordinaryAttachmentRim (⊥:SimpleGraph I) C z id
    let H := disjointWheelSpokes (I:=I) z
    HasOrdinaryWheelDecomposition G H r ∧
    (∀ a,G.degree a=2*(Finset.univ.filter (H a)).card) ∧
    (∀ b,r∣(Finset.univ.filter (fun a => H a b)).card) ∧
    G.edgeFinset.card=Fintype.card I*r ∧
    Fintype.card {e:(I⊕(I×W))×(Empty⊕I) // H e.1 e.2}=Fintype.card I*r := by
  dsimp only
  have hdec := ordinaryAttachment_extra_wheel_decomposition (V:=I) (U:=Empty) C hC z id hfull
  have hbal := ordinary_wheel_decomposition_balance _ _ r hdec
  have hcard : Fintype.card {e:(I⊕(I×W))×(Empty⊕I) // disjointWheelSpokes z e.1 e.2}=Fintype.card I*r := by
    rw [disjointWheelSpokes_card,hW]
  exact ⟨hdec,hbal.1,hbal.2,(ordinary_balanced_total_edges _ _ hbal.1).trans hcard,hcard⟩

end Oberwolfach
