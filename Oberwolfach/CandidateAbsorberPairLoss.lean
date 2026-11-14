module

public import Oberwolfach.CandidateAbsorberGroundRestriction

@[expose] public section

/-! A bound linear in the number of forbidden pairs, without an incident
degree or relative-size assumption on that pair set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C T : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T] {c : ℕ}

theorem absorberGroundCount_univ (R : C → Finset V) (S : T → VertexAbsorberTemplate c) (X : Finset V) :
    absorberGroundCount R S X Finset.univ=(Fintype.card (LabelledAbsorberFamily R S X):ℝ) := by
  unfold absorberGroundCount
  simp only [Finset.subset_univ,Fintype.card_subtype_true]

theorem candidate_absorber_pair_loss (hc : 2≤c) (hn : 1≤Fintype.card V)
    (R : C → Finset V) (S : T → VertexAbsorberTemplate c) (X : Finset V) (J : ℕ)
    (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y}≤J)
    (E : Finset (V×V)) (hE : ∀ e∈E,e.1≠e.2) :
    Fintype.card (LabelledAbsorberFamily R S X)≤
      Fintype.card (LabelledAbsorberFamily (candidateResourceSet R
        (fun C₀=>∀ e:E,¬(e.val.1∈R C₀ ∧ e.val.2∈R C₀))) S X)+
      E.card*(((c*c)+(c*c)^2)*Fintype.card T*X.card^c*(Fintype.card V)^(c*c-1)*J^(2*c+1)) := by
  have hh := candidate_absorber_ground_loss R
    (fun C₀=>∀ e:E,¬(e.val.1∈R C₀ ∧ e.val.2∈R C₀)) S X Finset.univ
  have he (D : LabelledAbsorberFamily R S X) :
      (labelledAbsorberFree R (S D.1) X D.2⊆Finset.univ ∧
        ¬∀ o,∀ e:E,¬(e.val.1∈R (D.2.2 o).val ∧ e.val.2∈R (D.2.2 o).val))↔
      (labelledAbsorberFree R (S D.1) X D.2⊆Finset.univ ∧
        ∃ e∈E,∃ o,e.1∈R (D.2.2 o).val ∧ e.2∈R (D.2.2 o).val) := by
    simp only [Finset.subset_univ,true_and,not_forall,not_not,Subtype.exists]
    aesop
  rw [Fintype.card_congr (Equiv.subtypeEquivRight he)] at hh
  rw [absorberGroundCount_univ,absorberGroundCount_univ] at hh
  have hb := labelled_absorber_forbidden_pairs_count R S X Finset.univ J hJ E hE
  simp only [Finset.card_univ] at hb
  have hp : (Fintype.card V)^(c*c-2)≤(Fintype.card V)^(c*c-1) :=
    Nat.pow_le_pow_right hn (by omega)
  have hb' : Fintype.card {D : LabelledAbsorberFamily R S X //
      labelledAbsorberFree R (S D.1) X D.2⊆Finset.univ ∧
      ∃ e∈E,∃ o,e.1∈R (D.2.2 o).val ∧ e.2∈R (D.2.2 o).val}≤
      E.card*(((c*c)+(c*c)^2)*Fintype.card T*X.card^c*(Fintype.card V)^(c*c-1)*J^(2*c+1)) := by
    apply hb.trans
    calc
      _ ≤ E.card*((c*c)*Fintype.card T*X.card^c*(Fintype.card V)^(c*c-1)*J^(2*c+1))+
          E.card*((c*c)^2*Fintype.card T*X.card^c*(Fintype.card V)^(c*c-1)*J^(2*c+1)) := by
        gcongr <;> first | exact Finset.filter_subset _ _ | exact hp
      _ = _ := by ring
  have hhN : Fintype.card (LabelledAbsorberFamily R S X)≤
      Fintype.card (LabelledAbsorberFamily (candidateResourceSet R
        (fun C₀=>∀ e:E,¬(e.val.1∈R C₀ ∧ e.val.2∈R C₀))) S X)+
      Fintype.card {D : LabelledAbsorberFamily R S X //
        labelledAbsorberFree R (S D.1) X D.2⊆Finset.univ ∧
        ∃ e∈E,∃ o,e.1∈R (D.2.2 o).val ∧ e.2∈R (D.2.2 o).val} := by exact_mod_cast hh
  exact hhN.trans (Nat.add_le_add_left hb' _)

end Oberwolfach
