module

public import Oberwolfach.TypedSumParts
public import Oberwolfach.MarkedTypedEndpointPairing

@[expose] public section

/-! The five endpoint graphs on tagged arc indices. An endpoint appearing
in both types remains two indices; its label fibre has size at most two. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def taggedSubsetValue {Z : Type} (A B : Finset Z) : A⊕B → Z := Sum.elim Subtype.val Subtype.val

theorem tagged_subset_label_fibre {Z : Type} (A B : Finset Z) (z : Z) :
    Fintype.card {a : A⊕B // taggedSubsetValue A B a=z}≤2 := by
  classical
  have hinj : Function.Injective (fun a : {a : A⊕B // taggedSubsetValue A B a=z}=>a.val.isRight) := by
    rintro ⟨a,ha⟩ ⟨b,hb⟩ he
    apply Subtype.ext
    cases a with
    | inl a=>cases b with
      | inl b=>exact congrArg Sum.inl (Subtype.ext (ha.trans hb.symm))
      | inr b=>cases he
    | inr a=>cases b with
      | inl b=>cases he
      | inr b=>exact congrArg Sum.inr (Subtype.ext (ha.trans hb.symm))
  simpa using Fintype.card_le_of_injective _ hinj

def markedIncomingAssignment (A₀ A₁ : Finset V) (Y₀ Y₁ : Finset U) (H₀ : V→U→Prop)
    (a : A₀⊕A₁) (y : Y₀⊕Y₁) : Prop :=
  a.isRight=y.isRight ∧ H₀ (taggedSubsetValue A₀ A₁ a) (taggedSubsetValue Y₀ Y₁ y)

def markedOutgoingAssignment (X₀ X₁ : Finset V) (Y₀ Y₁ : Finset U) (H₀ HK : V→U→Prop)
    (a : X₀⊕X₁) (y : Y₀⊕Y₁) : Prop :=
  ¬(a.isRight=true ∧ y.isRight=true) ∧
    if a.isRight then HK (taggedSubsetValue X₀ X₁ a) (taggedSubsetValue Y₀ Y₁ y)
    else H₀ (taggedSubsetValue X₀ X₁ a) (taggedSubsetValue Y₀ Y₁ y)

theorem marked_endpoint_assignment_blocks
    (A₀ A₁ X₀ X₁ : Finset V) (Y₀ Y₁ : Finset U) (H₀ HK : V→U→Prop)
    (d tau lam : ℝ)
    (B₁ : BipartiteBlockBounds H₀ (fun a=>a∈A₁) (fun y=>y∈Y₁) d tau lam)
    (B₂ : BipartiteBlockBounds H₀ (fun a=>a∈A₀) (fun y=>y∈Y₀) d tau lam)
    (B₃ : BipartiteBlockBounds HK (fun a=>a∈X₁) (fun y=>y∈Y₀) d tau lam)
    (B₄ : BipartiteBlockBounds H₀ (fun a=>a∈X₀) (fun y=>y∈Y₀) d tau lam)
    (B₅ : BipartiteBlockBounds H₀ (fun a=>a∈X₀) (fun y=>y∈Y₁) d tau lam) :
    BipartiteBlockBounds (markedIncomingAssignment A₀ A₁ Y₀ Y₁ H₀)
      (fun a=>a.isRight=true) (fun y=>y.isRight=true) d tau lam ∧
    BipartiteBlockBounds (markedIncomingAssignment A₀ A₁ Y₀ Y₁ H₀)
      (fun a=>¬a.isRight=true) (fun y=>¬y.isRight=true) d tau lam ∧
    BipartiteBlockBounds (markedOutgoingAssignment X₀ X₁ Y₀ Y₁ H₀ HK)
      (fun a=>a.isRight=true) (fun y=>¬y.isRight=true) d tau lam ∧
    BipartiteBlockBounds (markedOutgoingAssignment X₀ X₁ Y₀ Y₁ H₀ HK)
      (fun a=>¬a.isRight=true) (fun y=>¬y.isRight=true) d tau lam ∧
    BipartiteBlockBounds (markedOutgoingAssignment X₀ X₁ Y₀ Y₁ H₀ HK)
      (fun a=>¬a.isRight=true) (fun y=>y.isRight=true) d tau lam := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · apply bipartite_block_transport H₀ _ _ _ _ _ (typedSumRightEquiv A₀ A₁) (typedSumRightEquiv Y₀ Y₁) _ d tau lam B₁
    rintro ⟨a,ha⟩ ⟨y,hy⟩
    cases a <;> cases y
    all_goals first
      | exact False.elim (Bool.false_ne_true ha)
      | exact False.elim (Bool.false_ne_true hy)
      | exact False.elim (ha rfl)
      | exact False.elim (hy rfl)
      | simp [markedIncomingAssignment,taggedSubsetValue,typedSumRightEquiv]
  · apply bipartite_block_transport H₀ _ _ _ _ _ (typedSumLeftEquiv A₀ A₁) (typedSumLeftEquiv Y₀ Y₁) _ d tau lam B₂
    rintro ⟨a,ha⟩ ⟨y,hy⟩
    cases a <;> cases y
    all_goals first
      | exact False.elim (Bool.false_ne_true ha)
      | exact False.elim (Bool.false_ne_true hy)
      | exact False.elim (ha rfl)
      | exact False.elim (hy rfl)
      | simp [markedIncomingAssignment,taggedSubsetValue,typedSumLeftEquiv]
  · apply bipartite_block_transport HK _ _ _ _ _ (typedSumRightEquiv X₀ X₁) (typedSumLeftEquiv Y₀ Y₁) _ d tau lam B₃
    rintro ⟨a,ha⟩ ⟨y,hy⟩
    cases a <;> cases y
    all_goals first
      | exact False.elim (Bool.false_ne_true ha)
      | exact False.elim (Bool.false_ne_true hy)
      | exact False.elim (ha rfl)
      | exact False.elim (hy rfl)
      | simp [markedOutgoingAssignment,taggedSubsetValue,typedSumLeftEquiv,typedSumRightEquiv]
  · apply bipartite_block_transport H₀ _ _ _ _ _ (typedSumLeftEquiv X₀ X₁) (typedSumLeftEquiv Y₀ Y₁) _ d tau lam B₄
    rintro ⟨a,ha⟩ ⟨y,hy⟩
    cases a <;> cases y
    all_goals first
      | exact False.elim (Bool.false_ne_true ha)
      | exact False.elim (Bool.false_ne_true hy)
      | exact False.elim (ha rfl)
      | exact False.elim (hy rfl)
      | simp [markedOutgoingAssignment,taggedSubsetValue,typedSumLeftEquiv]
  · apply bipartite_block_transport H₀ _ _ _ _ _ (typedSumLeftEquiv X₀ X₁) (typedSumRightEquiv Y₀ Y₁) _ d tau lam B₅
    rintro ⟨a,ha⟩ ⟨y,hy⟩
    cases a <;> cases y
    all_goals first
      | exact False.elim (Bool.false_ne_true ha)
      | exact False.elim (Bool.false_ne_true hy)
      | exact False.elim (ha rfl)
      | exact False.elim (hy rfl)
      | simp [markedOutgoingAssignment,taggedSubsetValue,typedSumLeftEquiv,typedSumRightEquiv]

end Oberwolfach
