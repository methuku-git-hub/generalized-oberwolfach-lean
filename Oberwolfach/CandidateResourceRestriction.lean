module

public import Oberwolfach.ResourceRestriction
public import Oberwolfach.AbsorberFreeFamilies

@[expose] public section

/-! Restricting the indexed family by a predicate on cycle identifiers.
The vertex set, supports and weights of surviving cycles do not change. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 3600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C O T : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
    [Fintype O] [DecidableEq O] [Fintype T] [DecidableEq T] {h c : ℕ}

def candidateResourceSet (R : C → Finset V) (P : C → Prop) (D : {C₀ : C // P C₀}) : Finset V := R D.val

theorem candidate_resource_multiplicity (R : C → Finset V) (P : C → Prop) [DecidablePred P] (J : ℕ)
    (hJ : ∀ U : Finset V,Fintype.card {C₀ : C // R C₀=U} ≤ J) (U : Finset V) :
    Fintype.card {D : {C₀ : C // P C₀} // candidateResourceSet R P D=U} ≤ J := by
  let f : {D : {C₀ : C // P C₀} // candidateResourceSet R P D=U} → {C₀ : C // R C₀=U} :=
    fun D => ⟨D.val.val,D.property⟩
  have hi : Function.Injective f := by
    intro D E hh
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : {C₀ : C // R C₀=U} => z.val) hh
  exact (Fintype.card_le_of_injective f hi).trans (hJ U)

theorem candidate_resource_degree (R : C → Finset V) (P : C → Prop) [DecidablePred P] (w : C → ℝ) (v : V) :
    hypergraphWeightedDegree (candidateResourceSet R P) (fun D => w D.val) v=
      hypergraphWeightedDegree R (fun C₀ => if P C₀ then w C₀ else 0) v := by
  unfold hypergraphWeightedDegree
  have he := Finset.sum_subtype (F:=inferInstance) (p:=P)
    (Finset.univ.filter P) (fun _ => by simp) (fun C₀ => if v∈R C₀ then w C₀ else 0)
  change (∑ D : {C₀ : C // P C₀},if v∈R D.val then w D.val else 0)=_
  rw [← he,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro C₀ _
  by_cases hp : P C₀ <;> by_cases hv : v∈R C₀ <;> simp [hp,hv]

def filterLabelledRecord (R : C → Finset V) (P : C → Prop) [DecidablePred P]
    (S : O → Finset (Fin h ⊕ Fin c)) (X : Finset V)
    (D : {D : LabelledCycleRecord R S X // ∀ o,P (D.2 o).val}) :
    LabelledCycleRecord (candidateResourceSet R P) S X :=
  ⟨D.val.1,fun o => ⟨⟨(D.val.2 o).val,D.property o⟩,(D.val.2 o).property⟩⟩

theorem filterLabelledRecord_injective (R : C → Finset V) (P : C → Prop) [DecidablePred P]
    (S : O → Finset (Fin h ⊕ Fin c)) (X : Finset V) :
    Function.Injective (filterLabelledRecord R P S X) := by
  intro D E he
  apply Subtype.ext
  apply labelledCycleRecord_ext R S X D.val E.val
  · intro j
    exact congrArg (fun D : LabelledCycleRecord (candidateResourceSet R P) S X => D.1.val j) he
  · intro o
    exact congrArg (fun D : LabelledCycleRecord (candidateResourceSet R P) S X => (D.2 o).val.val) he

def filterAbsorberFamily (R : C → Finset V) (P : C → Prop) [DecidablePred P]
    (S : T → VertexAbsorberTemplate c) (X : Finset V)
    (D : {D : LabelledAbsorberFamily R S X // ∀ o,P (D.2.2 o).val}) :
    LabelledAbsorberFamily (candidateResourceSet R P) S X :=
  ⟨D.val.1,filterLabelledRecord R P (S D.val.1).val X ⟨D.val.2,D.property⟩⟩

theorem filterAbsorberFamily_injective (R : C → Finset V) (P : C → Prop) [DecidablePred P]
    (S : T → VertexAbsorberTemplate c) (X : Finset V) :
    Function.Injective (filterAbsorberFamily R P S X) := by
  intro D E he
  apply Subtype.ext
  apply labelledAbsorberFamily_ext R S X D.val E.val
  · exact congrArg (fun D : LabelledAbsorberFamily (candidateResourceSet R P) S X => D.1) he
  · intro j
    exact congrArg (fun D : LabelledAbsorberFamily (candidateResourceSet R P) S X => D.2.1.val j) he
  · intro o
    exact congrArg (fun D : LabelledAbsorberFamily (candidateResourceSet R P) S X => (D.2.2 o).val.val) he

theorem candidate_absorber_family_card (R : C → Finset V) (P : C → Prop) [DecidablePred P]
    (S : T → VertexAbsorberTemplate c) (X : Finset V) :
    Fintype.card {D : LabelledAbsorberFamily R S X // ∀ o,P (D.2.2 o).val} ≤
      Fintype.card (LabelledAbsorberFamily (candidateResourceSet R P) S X) :=
  Fintype.card_le_of_injective _ (filterAbsorberFamily_injective R P S X)

theorem candidate_absorber_card_loss (R : C → Finset V) (P : C → Prop) [DecidablePred P]
    (S : T → VertexAbsorberTemplate c) (X : Finset V) :
    Fintype.card (LabelledAbsorberFamily R S X) ≤
      Fintype.card (LabelledAbsorberFamily (candidateResourceSet R P) S X)+
      Fintype.card {D : LabelledAbsorberFamily R S X // ¬∀ o,P (D.2.2 o).val} := by
  let Q (D : LabelledAbsorberFamily R S X) := ∀ o,P (D.2.2 o).val
  have hgood := candidate_absorber_family_card R P S X
  have hbad := Fintype.card_subtype_compl Q
  have hle := Fintype.card_subtype_le Q
  change Fintype.card {D // Q D} ≤ _ at hgood
  change _ ≤ _+Fintype.card {D // ¬Q D}
  omega

theorem candidate_resource_decomposition_lift (R : C → Finset V) (P : C → Prop) [DecidablePred P]
    (U : Finset V) (h : HasResourceDecomposition (candidateResourceSet R P) U) :
    ∃ D : Finset C,((∀ x∈D,∀ y∈D,x≠y → Disjoint (R x) (R y)) ∧ D.biUnion R=U) ∧ ∀ C₀∈D,P C₀ := by
  obtain ⟨D,hD⟩ := h
  refine ⟨D.image Subtype.val,?_,?_⟩
  · refine ⟨?_,?_⟩
    · intro x hx y hy hxy
      obtain ⟨x',hx',rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨y',hy',rfl⟩ := Finset.mem_image.mp hy
      exact hD.1 x' hx' y' hy' (fun hh => hxy (congrArg Subtype.val hh))
    · rw [Finset.image_biUnion]
      exact hD.2
  · intro C₀ hC
    obtain ⟨D₀,_,rfl⟩ := Finset.mem_image.mp hC
    exact D₀.property

end Oberwolfach
