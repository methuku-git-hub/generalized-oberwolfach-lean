module

public import Oberwolfach.LabelledLocalPairCounts
public import Oberwolfach.AbsorberOccurrenceRoots
public import Oberwolfach.FiniteSubsetSums

@[expose] public section

/-! Explicit losses from forbidden displayed endpoint pairs. This
bound preserves all templates, label maps and indexed cycle choices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C T : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
    [Fintype T] [DecidableEq T] {c : ℕ}

theorem labelled_absorber_forbidden_pair_count (R : C → Finset V)
    (S : T → VertexAbsorberTemplate c) (X Y : Finset V) (J : ℕ)
    (hJ : ∀ U : Finset V,Fintype.card {C₀ : C // R C₀=U} ≤ J)
    (x y : V) (hxy : x≠y) :
    Fintype.card {D : LabelledAbsorberFamily R S X //
      labelledAbsorberFree R (S D.1) X D.2⊆Y ∧
      ∃ o,x∈R (D.2.2 o).val ∧ y∈R (D.2.2 o).val} ≤
      if x∈X ∨ y∈X then (c*c)*Fintype.card T*X.card^c*Y.card^(c*c-1)*J^(2*c+1)
      else (c*c)^2*Fintype.card T*X.card^c*Y.card^(c*c-2)*J^(2*c+1) := by
  let F := LabelledAbsorberFamily R S X
  by_cases hx : x∈X
  · rw [if_pos (Or.inl hx)]
    apply (Fintype.card_subtype_mono _
      (fun D : F => labelledAbsorberFree R (S D.1) X D.2⊆Y ∧
        y∈labelledAbsorberFree R (S D.1) X D.2) ?_).trans
      (labelled_absorber_local_free_vertex_count R S X Y J hJ y)
    rintro D ⟨hD,o,hxo,hyo⟩
    refine ⟨hD,?_⟩
    have hy : y∉X := fun hy => hxy
      (labelled_absorber_occurrence_root_unique R (S D.1) X D.2 o x y hxo hyo hx hy)
    exact (Finset.mem_union.mp (labelled_absorber_occurrence_subset R (S D.1) X D.2 o hyo)).resolve_right hy
  · by_cases hy : y∈X
    · rw [if_pos (Or.inr hy)]
      apply (Fintype.card_subtype_mono _
        (fun D : F => labelledAbsorberFree R (S D.1) X D.2⊆Y ∧
          x∈labelledAbsorberFree R (S D.1) X D.2) ?_).trans
        (labelled_absorber_local_free_vertex_count R S X Y J hJ x)
      rintro D ⟨hD,o,hxo,hyo⟩
      exact ⟨hD,(Finset.mem_union.mp
        (labelled_absorber_occurrence_subset R (S D.1) X D.2 o hxo)).resolve_right hx⟩
    · rw [if_neg (not_or.mpr ⟨hx,hy⟩)]
      apply (Fintype.card_subtype_mono _
        (fun D : F => labelledAbsorberFree R (S D.1) X D.2⊆Y ∧
          x∈labelledAbsorberFree R (S D.1) X D.2 ∧
          y∈labelledAbsorberFree R (S D.1) X D.2) ?_).trans
        (labelled_absorber_local_free_pair_count R S X Y J hJ x y hxy)
      rintro D ⟨hD,o,hxo,hyo⟩
      exact ⟨hD,(Finset.mem_union.mp
        (labelled_absorber_occurrence_subset R (S D.1) X D.2 o hxo)).resolve_right hx,
        (Finset.mem_union.mp
        (labelled_absorber_occurrence_subset R (S D.1) X D.2 o hyo)).resolve_right hy⟩

theorem labelled_absorber_forbidden_pairs_count (R : C → Finset V)
    (S : T → VertexAbsorberTemplate c) (X Y : Finset V) (J : ℕ)
    (hJ : ∀ U : Finset V,Fintype.card {C₀ : C // R C₀=U} ≤ J)
    (E : Finset (V×V)) (hE : ∀ e∈E,e.1≠e.2) :
    Fintype.card {D : LabelledAbsorberFamily R S X //
      labelledAbsorberFree R (S D.1) X D.2⊆Y ∧
      ∃ e∈E,∃ o,e.1∈R (D.2.2 o).val ∧ e.2∈R (D.2.2 o).val} ≤
      (E.filter (fun e => e.1∈X ∨ e.2∈X)).card*
        ((c*c)*Fintype.card T*X.card^c*Y.card^(c*c-1)*J^(2*c+1))+
      (E.filter (fun e => ¬(e.1∈X ∨ e.2∈X))).card*
        ((c*c)^2*Fintype.card T*X.card^c*Y.card^(c*c-2)*J^(2*c+1)) := by
  let F := LabelledAbsorberFamily R S X
  let Q (e : E) (D : F) := labelledAbsorberFree R (S D.1) X D.2⊆Y ∧
    ∃ o,e.val.1∈R (D.2.2 o).val ∧ e.val.2∈R (D.2.2 o).val
  have he (D : F) : (labelledAbsorberFree R (S D.1) X D.2⊆Y ∧
      ∃ e∈E,∃ o,e.1∈R (D.2.2 o).val ∧ e.2∈R (D.2.2 o).val) ↔ ∃ e,Q e D := by
    constructor
    · rintro ⟨hD,e,he,o,h₁,h₂⟩;exact ⟨⟨e,he⟩,hD,o,h₁,h₂⟩
    · rintro ⟨e,hD,o,h₁,h₂⟩;exact ⟨hD,e.val,e.property,o,h₁,h₂⟩
  let A := Finset.univ.filter (fun D : F => labelledAbsorberFree R (S D.1) X D.2⊆Y ∧
    ∃ e∈E,∃ o,e.1∈R (D.2.2 o).val ∧ e.2∈R (D.2.2 o).val)
  let B := fun e : E => Finset.univ.filter (Q e)
  have hsub : A⊆Finset.univ.biUnion B := by
    intro D hD
    obtain ⟨e,heD⟩ := (he D).mp (Finset.mem_filter.mp hD).2
    exact Finset.mem_biUnion.mpr ⟨e,Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,heD⟩⟩
  simp only [Fintype.card_subtype]
  change A.card ≤ _
  calc
    _ ≤ (Finset.univ.biUnion B).card := Finset.card_le_card hsub
    _ ≤ ∑ e : E,(B e).card := Finset.card_biUnion_le
    _ ≤ ∑ e : E,if e.val.1∈X ∨ e.val.2∈X then
        (c*c)*Fintype.card T*X.card^c*Y.card^(c*c-1)*J^(2*c+1)
      else (c*c)^2*Fintype.card T*X.card^c*Y.card^(c*c-2)*J^(2*c+1) := by
        apply Finset.sum_le_sum
        intro e _
        simpa only [Fintype.card_subtype,B,Q] using
          labelled_absorber_forbidden_pair_count R S X Y J hJ e.val.1 e.val.2 (hE e.val e.property)
    _ = _ := by
      convert finite_subset_ite_sum (A:=ℕ) E (fun e => e.1∈X ∨ e.2∈X)
        ((c*c)*Fintype.card T*X.card^c*Y.card^(c*c-1)*J^(2*c+1))
        ((c*c)^2*Fintype.card T*X.card^c*Y.card^(c*c-2)*J^(2*c+1)) using 1 <;> congr! <;> (try simp only [Nat.cast_id]) <;> congr!

end Oberwolfach
