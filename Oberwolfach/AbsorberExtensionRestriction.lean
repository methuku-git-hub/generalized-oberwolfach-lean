module

public import Oberwolfach.AbsorberOccurrenceRoots
public import Oberwolfach.CandidateResourceRestriction
public import Oberwolfach.AbsorberProfileSampling

@[expose] public section

/-! Absorbers whose free vertices lie outside a prescribed set remain
valid when each cycle is required to meet that set at most once. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C T : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
    [Fintype T] [DecidableEq T] {c : ℕ}

theorem labelled_absorber_extension_occurrence (R : C → Finset V)
    (S : VertexAbsorberTemplate c) (X A Z : Finset V) (hAZ : Disjoint A Z)
    (D : LabelledCycleRecord R S.val X)
    (hfree : labelledAbsorberFree R S X D⊆A) (o : Fin c ⊕ Fin (c+1)) :
    (R (D.2 o).val∩Z).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨hx,hxZ⟩ := Finset.mem_inter.mp hx
  obtain ⟨hy,hyZ⟩ := Finset.mem_inter.mp hy
  have hxX : x∈X := by
    have hh := Finset.mem_union.mp (labelled_absorber_occurrence_subset R S X D o hx)
    exact hh.resolve_left (fun hf => Finset.disjoint_left.mp hAZ (hfree hf) hxZ)
  have hyX : y∈X := by
    have hh := Finset.mem_union.mp (labelled_absorber_occurrence_subset R S X D o hy)
    exact hh.resolve_left (fun hf => Finset.disjoint_left.mp hAZ (hfree hf) hyZ)
  exact labelled_absorber_occurrence_root_unique R S X D o x y hx hy hxX hyX

theorem absorber_extension_candidate_count (R : C → Finset V)
    (S : T → VertexAbsorberTemplate c) (X A Z : Finset V) (hAZ : Disjoint A Z) :
    absorberGroundCount R S X A ≤
      Fintype.card (LabelledAbsorberFamily
        (candidateResourceSet R (fun C₀ => (R C₀∩Z).card ≤ 1)) S X) := by
  let P := fun C₀ => (R C₀∩Z).card ≤ 1
  let D₀ := {D : LabelledAbsorberFamily R S X // labelledAbsorberFree R (S D.1) X D.2⊆A}
  let D₁ := {D : LabelledAbsorberFamily R S X // ∀ o,P (D.2.2 o).val}
  let f : D₀ → D₁ := fun D => ⟨D.val,fun o =>
    labelled_absorber_extension_occurrence R (S D.val.1) X A Z hAZ D.val.2 D.property o⟩
  have hf : Function.Injective f := by
    intro D E hh
    apply Subtype.ext
    exact congrArg (fun D : D₁ => D.val) hh
  have hh := (Fintype.card_le_of_injective f hf).trans (candidate_absorber_family_card R P S X)
  unfold absorberGroundCount
  convert (show (Fintype.card D₀:ℝ) ≤ Fintype.card (LabelledAbsorberFamily (candidateResourceSet R P) S X) by exact_mod_cast hh) using 1 <;> congr!


theorem absorber_extension_ground_count (R : C → Finset V)
    (S : T → VertexAbsorberTemplate c) (X A Y Z : Finset V)
    (hAZ : Disjoint A Z) (hAY : A⊆Y) :
    absorberGroundCount R S X A ≤
      absorberGroundCount (candidateResourceSet R (fun C₀ => (R C₀∩Z).card ≤ 1)) S X Y := by
  let P := fun C₀ => (R C₀∩Z).card ≤ 1
  let D₀ := {D : LabelledAbsorberFamily R S X // labelledAbsorberFree R (S D.1) X D.2⊆A}
  let D₁ := {D : LabelledAbsorberFamily (candidateResourceSet R P) S X //
    labelledAbsorberFree (candidateResourceSet R P) (S D.1) X D.2⊆Y}
  let f : D₀ → D₁ := fun D => ⟨filterAbsorberFamily R P S X
    ⟨D.val,fun o => labelled_absorber_extension_occurrence R (S D.val.1) X A Z hAZ D.val.2 D.property o⟩,
    D.property.trans hAY⟩
  have hf : Function.Injective f := by
    intro D E hh
    have hfilter := congrArg (fun D : D₁ => D.val) hh
    have hraw := filterAbsorberFamily_injective R P S X hfilter
    apply Subtype.ext
    exact congrArg (fun D : {D : LabelledAbsorberFamily R S X // ∀ o,P (D.2.2 o).val} => D.val) hraw
  have hh := Fintype.card_le_of_injective f hf
  unfold absorberGroundCount
  exact_mod_cast hh

end Oberwolfach
