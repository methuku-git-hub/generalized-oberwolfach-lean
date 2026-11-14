module

public import Oberwolfach.CandidateResourceRestriction
public import Oberwolfach.AbsorberProfileSampling

@[expose] public section

/-! Changing cycle identifiers while retaining their vertex sets preserves
all labelled absorber records, including their root and free-label maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C D O T : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
    [Fintype O] [DecidableEq O] [Fintype T] [DecidableEq T] {h c : ℕ}

def embedLabelledCycleRecord (R : C → Finset V) (R' : D → Finset V)
    (f : C ↪ D) (hf : ∀ i,R' (f i)=R i)
    (S : O → Finset (Fin h ⊕ Fin c)) (X : Finset V)
    (A : LabelledCycleRecord R S X) : LabelledCycleRecord R' S X :=
  ⟨A.1,fun o=>⟨f (A.2 o).val,(hf _).trans (A.2 o).property⟩⟩

theorem embedLabelledCycleRecord_injective (R : C → Finset V) (R' : D → Finset V)
    (f : C ↪ D) (hf : ∀ i,R' (f i)=R i)
    (S : O → Finset (Fin h ⊕ Fin c)) (X : Finset V) :
    Function.Injective (embedLabelledCycleRecord R R' f hf S X) := by
  intro A B he
  apply labelledCycleRecord_ext R S X A B
  · intro j
    exact congrArg (fun D : LabelledCycleRecord R' S X=>D.1.val j) he
  · intro o
    exact f.injective (congrArg (fun D : LabelledCycleRecord R' S X=>(D.2 o).val) he)

def embedAbsorberFamily (R : C → Finset V) (R' : D → Finset V)
    (f : C ↪ D) (hf : ∀ i,R' (f i)=R i)
    (S : T → VertexAbsorberTemplate c) (X : Finset V)
    (A : LabelledAbsorberFamily R S X) : LabelledAbsorberFamily R' S X :=
  ⟨A.1,embedLabelledCycleRecord R R' f hf (S A.1).val X A.2⟩

theorem embedAbsorberFamily_injective (R : C → Finset V) (R' : D → Finset V)
    (f : C ↪ D) (hf : ∀ i,R' (f i)=R i)
    (S : T → VertexAbsorberTemplate c) (X : Finset V) :
    Function.Injective (embedAbsorberFamily R R' f hf S X) := by
  intro A B he
  apply labelledAbsorberFamily_ext R S X A B
  · exact congrArg (fun D : LabelledAbsorberFamily R' S X=>D.1) he
  · intro j
    exact congrArg (fun D : LabelledAbsorberFamily R' S X=>D.2.1.val j) he
  · intro o
    exact f.injective (congrArg (fun D : LabelledAbsorberFamily R' S X=>(D.2.2 o).val) he)

theorem absorber_family_card_embedding (R : C → Finset V) (R' : D → Finset V)
    (f : C ↪ D) (hf : ∀ i,R' (f i)=R i)
    (S : T → VertexAbsorberTemplate c) (X : Finset V) :
    Fintype.card (LabelledAbsorberFamily R S X)≤Fintype.card (LabelledAbsorberFamily R' S X) :=
  Fintype.card_le_of_injective _ (embedAbsorberFamily_injective R R' f hf S X)

theorem absorber_ground_count_embedding (R : C → Finset V) (R' : D → Finset V)
    (f : C ↪ D) (hf : ∀ i,R' (f i)=R i)
    (S : T → VertexAbsorberTemplate c) (X Y : Finset V) :
    absorberGroundCount R S X Y≤absorberGroundCount R' S X Y := by
  let A := {D : LabelledAbsorberFamily R S X // labelledAbsorberFree R (S D.1) X D.2⊆Y}
  let B := {D : LabelledAbsorberFamily R' S X // labelledAbsorberFree R' (S D.1) X D.2⊆Y}
  let g : A → B := fun a=>⟨embedAbsorberFamily R R' f hf S X a.val,a.property⟩
  have hg : Function.Injective g := by
    intro a b he
    apply Subtype.ext
    exact embedAbsorberFamily_injective R R' f hf S X (congrArg Subtype.val he)
  change (Fintype.card A:ℝ)≤(Fintype.card B:ℝ)
  exact_mod_cast Fintype.card_le_of_injective g hg

end Oberwolfach
