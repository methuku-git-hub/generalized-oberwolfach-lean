module

public import Oberwolfach.CandidateResourceRestriction
public import Oberwolfach.AbsorberProfileSampling
public import Oberwolfach.BoundedPairDeletionLoss

@[expose] public section

/-! Candidate restriction with the free-vertex set retained in every
count. This avoids replacing a local absorber count by a global count. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 256
set_option maxHeartbeats 3600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C T : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
    [Fintype T] [DecidableEq T] {c : ℕ}

theorem candidate_absorber_ground_loss (R : C → Finset V) (P : C → Prop) [DecidablePred P]
    (S : T → VertexAbsorberTemplate c) (X Y : Finset V) :
    absorberGroundCount R S X Y ≤
      absorberGroundCount (candidateResourceSet R P) S X Y+
      Fintype.card {D : LabelledAbsorberFamily R S X //
        labelledAbsorberFree R (S D.1) X D.2⊆Y ∧ ¬∀ o,P (D.2.2 o).val} := by
  let D := LabelledAbsorberFamily R S X
  let F := fun d : D => labelledAbsorberFree R (S d.1) X d.2⊆Y
  let Q := fun d : D => ∀ o,P (d.2.2 o).val
  let G := {d : D // F d ∧ Q d}
  let H := {d : LabelledAbsorberFamily (candidateResourceSet R P) S X //
    labelledAbsorberFree (candidateResourceSet R P) (S d.1) X d.2⊆Y}
  let f : G → H := fun d => ⟨filterAbsorberFamily R P S X ⟨d.val,d.property.2⟩,d.property.1⟩
  have hf : Function.Injective f := by
    intro d e he
    have hh := filterAbsorberFamily_injective R P S X (congrArg (fun d : H => d.val) he)
    apply Subtype.ext
    exact congrArg (fun d : {d : D // Q d} => d.val) hh
  have hg := Fintype.card_le_of_injective f hf
  have hpart : Fintype.card {d : D // F d} ≤ Fintype.card G+Fintype.card {d : D // F d ∧ ¬Q d} := by
    simp only [Fintype.card_subtype,G]
    have he : Finset.univ.filter F=(Finset.univ.filter (fun d => F d∧Q d))∪
        (Finset.univ.filter (fun d => F d∧¬Q d)) := by
      ext d
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
      tauto
    rw [he]
    exact Finset.card_union_le _ _
  have htotal := hpart.trans (Nat.add_le_add_right hg _)
  unfold absorberGroundCount
  exact_mod_cast htotal

theorem candidate_absorber_ground_bounded_pair_loss (hc : 2 ≤ c) (R : C → Finset V)
    (S : T → VertexAbsorberTemplate c) (X Y : Finset V) (J : ℕ)
    (hJ : ∀ U : Finset V,Fintype.card {C₀ : C // R C₀=U} ≤ J)
    (E : Finset (V×V)) (hE : ∀ e∈E,e.1≠e.2) (d : ℕ)
    (hd : ∀ v∈X,(E.filter (fun e => v=e.1 ∨ v=e.2)).card ≤ d)
    (hsize : E.card ≤ Y.card) :
    absorberGroundCount R S X Y ≤
      absorberGroundCount (candidateResourceSet R
        (fun C₀ => ∀ e : E,¬(e.val.1∈R C₀ ∧ e.val.2∈R C₀))) S X Y+
      ((X.card*d*(c*c)+(c*c)^2)*Fintype.card T*X.card^c*Y.card^(c*c-1)*J^(2*c+1):ℕ) := by
  let P := fun C₀ => ∀ e : E,¬(e.val.1∈R C₀ ∧ e.val.2∈R C₀)
  letI : DecidablePred P := Classical.decPred P
  have hh := candidate_absorber_ground_loss R P S X Y
  have he (D : LabelledAbsorberFamily R S X) :
      (labelledAbsorberFree R (S D.1) X D.2⊆Y ∧ ¬∀ o,P (D.2.2 o).val) ↔
      (labelledAbsorberFree R (S D.1) X D.2⊆Y ∧
        ∃ e∈E,∃ o,e.1∈R (D.2.2 o).val ∧ e.2∈R (D.2.2 o).val) := by
    simp only [P,not_forall,not_not,Subtype.exists]
    tauto
  have heq := Fintype.card_congr (Equiv.subtypeEquivRight he)
  rw [heq] at hh
  have hb := labelled_absorber_bounded_pair_loss hc R S X Y J hJ E hE d hd hsize
  apply hh.trans
  have hbR : (Fintype.card {D : LabelledAbsorberFamily R S X //
      labelledAbsorberFree R (S D.1) X D.2⊆Y ∧
        ∃ e∈E,∃ o,e.1∈R (D.2.2 o).val ∧ e.2∈R (D.2.2 o).val}:ℝ) ≤
      ((X.card*d*(c*c)+(c*c)^2)*Fintype.card T*X.card^c*Y.card^(c*c-1)*J^(2*c+1):ℕ) := by
    exact_mod_cast hb
  convert add_le_add (le_refl (absorberGroundCount (candidateResourceSet R P) S X Y)) hbR using 1 <;> congr!

end Oberwolfach
