module

public import Oberwolfach.BoundedPairDeletionLoss
public import Oberwolfach.CandidateResourceRestriction

@[expose] public section

/-! Losses for sparse forbidden endpoint pairs at the original class
scale. These formulas keep the weights and cycle identifiers fixed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 256
set_option maxHeartbeats 500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C T : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
    [Fintype T] [DecidableEq T] {c : ℕ}

def absorberPairDeletionCoefficient (c J N d : ℕ) : ℝ :=
  ((c*d*(c*c)+(c*c)^2):ℕ)*N*(c:ℝ)^c*(c:ℝ)^(c*c-1)*(J:ℝ)^(2*c+1)

theorem candidate_absorber_pair_loss_scale (hc : 2 ≤ c) (R : C → Finset V)
    (S : T → VertexAbsorberTemplate c) (X : Finset V) (J : ℕ)
    (hJ : ∀ U : Finset V,Fintype.card {C₀ : C // R C₀=U} ≤ J)
    (E : Finset (V×V)) (hE : ∀ e∈E,e.1≠e.2) (d : ℕ)
    (hd : ∀ v∈X,(E.filter (fun e => v=e.1 ∨ v=e.2)).card ≤ d)
    (hsize : E.card ≤ Fintype.card V) (k : ℝ) (hn : (Fintype.card V:ℝ)=c*k) (hX : X.card=c) :
    (Fintype.card (LabelledAbsorberFamily R S X):ℝ) ≤
      Fintype.card (LabelledAbsorberFamily (candidateResourceSet R
        (fun C₀ => ∀ e : E,¬(e.val.1∈R C₀ ∧ e.val.2∈R C₀))) S X)+
      absorberPairDeletionCoefficient c J (Fintype.card T) d*k^(c*c-1) := by
  let P := fun C₀ => ∀ e : E,¬(e.val.1∈R C₀ ∧ e.val.2∈R C₀)
  letI : DecidablePred P := Classical.decPred P
  have hloss := candidate_absorber_card_loss R P S X
  have hbad := labelled_absorber_bounded_pair_loss hc R S X Finset.univ J hJ E hE d hd
    (by simpa only [Finset.card_univ] using hsize)
  have hmono : Fintype.card {D : LabelledAbsorberFamily R S X // ¬∀ o,P (D.2.2 o).val} ≤
      Fintype.card {D : LabelledAbsorberFamily R S X //
        labelledAbsorberFree R (S D.1) X D.2⊆Finset.univ ∧
          ∃ e∈E,∃ o,e.1∈R (D.2.2 o).val ∧ e.2∈R (D.2.2 o).val} := by
    apply Fintype.card_subtype_mono
    intro D hD
    obtain ⟨o,ho⟩ := not_forall.mp hD
    obtain ⟨e,he⟩ := not_forall.mp ho
    exact ⟨Finset.subset_univ _,e.val,e.property,o,not_not.mp he⟩
  have hbad' : Fintype.card {D : LabelledAbsorberFamily R S X //
        labelledAbsorberFree R (S D.1) X D.2⊆Finset.univ ∧
          ∃ e∈E,∃ o,e.1∈R (D.2.2 o).val ∧ e.2∈R (D.2.2 o).val} ≤
      (X.card*d*(c*c)+(c*c)^2)*Fintype.card T*X.card^c*(Finset.univ : Finset V).card^(c*c-1)*J^(2*c+1) := by
    convert hbad using 1 <;> congr!
  have hh : Fintype.card (LabelledAbsorberFamily R S X) ≤
      Fintype.card (LabelledAbsorberFamily (candidateResourceSet R P) S X)+
      (X.card*d*(c*c)+(c*c)^2)*Fintype.card T*X.card^c*(Finset.univ : Finset V).card^(c*c-1)*J^(2*c+1) := by
    calc
      _ ≤ Fintype.card (LabelledAbsorberFamily (candidateResourceSet R P) S X)+
          Fintype.card {D : LabelledAbsorberFamily R S X // ¬∀ o,P (D.2.2 o).val} := by
        convert hloss using 1 <;> congr!
      _ ≤ _ := by
        apply Nat.add_le_add_left
        calc
          _ ≤ Fintype.card {D : LabelledAbsorberFamily R S X //
              labelledAbsorberFree R (S D.1) X D.2⊆Finset.univ ∧
                ∃ e∈E,∃ o,e.1∈R (D.2.2 o).val ∧ e.2∈R (D.2.2 o).val} := by
            convert hmono using 1 <;> congr!
          _ ≤ _ := by convert hbad' using 1 <;> congr!
  rw [Finset.card_univ,hX] at hh
  have hhR : (Fintype.card (LabelledAbsorberFamily R S X):ℝ) ≤
      Fintype.card (LabelledAbsorberFamily (candidateResourceSet R P) S X)+
      ((c*d*(c*c)+(c*c)^2):ℕ)*(Fintype.card T:ℝ)*(c:ℝ)^c*(Fintype.card V:ℝ)^(c*c-1)*(J:ℝ)^(2*c+1) := by
    exact_mod_cast hh
  rw [hn] at hhR
  have heK : ((c*d*(c*c)+(c*c)^2):ℕ)*(Fintype.card T:ℝ)*(c:ℝ)^c*
      ((c:ℝ)*k)^(c*c-1)*(J:ℝ)^(2*c+1)=
      absorberPairDeletionCoefficient c J (Fintype.card T) d*k^(c*c-1) := by
    dsimp [absorberPairDeletionCoefficient]
    simp only [mul_pow]
    ring
  rw [heK] at hhR
  convert hhR using 1 <;> congr!

theorem candidate_resource_pair_degree_loss_scale (R : C → Finset V) (c J : ℕ) (hc : 3 ≤ c)
    (hR : ∀ C₀,(R C₀).card=c) (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J)
    (w : C → ℝ) (B k : ℝ) (hB : 0 ≤ B) (hk : 0 < k)
    (hn : (Fintype.card V:ℝ)=c*k) (hw : ∀ C₀,0 ≤ w C₀ ∧ w C₀ ≤ B/k^(c-1))
    (E : Finset (V×V)) (hE : ∀ e∈E,e.1≠e.2) (v : V) (d : ℕ)
    (hd : (E.filter (fun e => v=e.1 ∨ v=e.2)).card ≤ d) (hsize : E.card ≤ Fintype.card V) :
    0 ≤ hypergraphWeightedDegree R w v-
      hypergraphWeightedDegree (candidateResourceSet R
        (fun C₀ => ∀ e : E,¬(e.val.1∈R C₀ ∧ e.val.2∈R C₀))) (fun D => w D.val) v ∧
    hypergraphWeightedDegree R w v-
      hypergraphWeightedDegree (candidateResourceSet R
        (fun C₀ => ∀ e : E,¬(e.val.1∈R C₀ ∧ e.val.2∈R C₀))) (fun D => w D.val) v ≤
      (((d:ℝ)+1)*(J:ℝ)*(c:ℝ)^(c-2)*B)/k := by
  have hh := resource_bounded_pairs_degree_loss R c J hc hR hJ w (B/k^(c-1)) (by positivity) hw
    Finset.univ E hE v d hd (by simpa only [Finset.card_univ] using hsize)
  have he : inducedResourceWeight R w Finset.univ=w := by funext C₀;simp [inducedResourceWeight]
  rw [he,Finset.card_univ,hn,mul_pow] at hh
  have hpow : k^(c-1)=k^(c-2)*k := by rw [← pow_succ];congr 1;omega
  have heq : ((d:ℝ)+1)*(J:ℝ)*((c:ℝ)^(c-2)*k^(c-2))*(B/k^(c-1))=
      (((d:ℝ)+1)*(J:ℝ)*(c:ℝ)^(c-2)*B)/k := by
    rw [hpow]
    field_simp
  rw [heq] at hh
  have hdeg : hypergraphWeightedDegree (candidateResourceSet R
      (fun C₀ => ∀ e : E,¬(e.val.1∈R C₀ ∧ e.val.2∈R C₀))) (fun D => w D.val) v=
      hypergraphWeightedDegree R (pairRestrictedResourceWeight R w E) v := by
    convert candidate_resource_degree R (fun C₀ => ∀ e : E,¬(e.val.1∈R C₀ ∧ e.val.2∈R C₀)) w v using 1 <;> congr! <;> unfold pairRestrictedResourceWeight <;> congr!
  rw [hdeg]
  exact hh

end Oberwolfach
