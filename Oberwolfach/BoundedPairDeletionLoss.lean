module

public import Oberwolfach.AbsorberForbiddenPairCounts
public import Oberwolfach.ResourceForbiddenPairWeights
public import Oberwolfach.FinitePairIncidence

@[expose] public section

/-! Quantitative deletion bounds for a set of displayed pairs with
bounded incidence and at most as many pairs as local vertices. -/
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

theorem labelled_absorber_bounded_pair_loss (hc : 2 ≤ c) (R : C → Finset V)
    (S : T → VertexAbsorberTemplate c) (X Y : Finset V) (J : ℕ)
    (hJ : ∀ U : Finset V,Fintype.card {C₀ : C // R C₀=U} ≤ J)
    (E : Finset (V×V)) (hE : ∀ e∈E,e.1≠e.2) (d : ℕ)
    (hd : ∀ v∈X,(E.filter (fun e => v=e.1 ∨ v=e.2)).card ≤ d)
    (hsize : E.card ≤ Y.card) :
    Fintype.card {D : LabelledAbsorberFamily R S X //
      labelledAbsorberFree R (S D.1) X D.2⊆Y ∧
      ∃ e∈E,∃ o,e.1∈R (D.2.2 o).val ∧ e.2∈R (D.2.2 o).val} ≤
      (X.card*d*(c*c)+(c*c)^2)*Fintype.card T*X.card^c*Y.card^(c*c-1)*J^(2*c+1) := by
  have h₁ := finite_pairs_incident_set_card E X d hd
  have h₂ : (E.filter (fun e => ¬(e.1∈X ∨ e.2∈X))).card ≤ Y.card := (Finset.card_filter_le _ _).trans hsize
  have hh := labelled_absorber_forbidden_pairs_count R S X Y J hJ E hE
  have he : Y.card*Y.card^(c*c-2)=Y.card^(c*c-1) := by
    rw [← pow_succ']
    congr 1
    have hcc : 2 ≤ c*c := by nlinarith
    omega
  apply hh.trans
  calc
    _ ≤ X.card*d*((c*c)*Fintype.card T*X.card^c*Y.card^(c*c-1)*J^(2*c+1))+
        Y.card*((c*c)^2*Fintype.card T*X.card^c*Y.card^(c*c-2)*J^(2*c+1)) :=
      Nat.add_le_add (Nat.mul_le_mul_right _ h₁) (Nat.mul_le_mul_right _ h₂)
    _ = _ := by rw [← he];ring

theorem resource_bounded_pairs_degree_loss (R : C → Finset V) (c J : ℕ) (hc : 3 ≤ c)
    (hR : ∀ C₀,(R C₀).card=c) (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J)
    (w : C → ℝ) (B : ℝ) (hB : 0 ≤ B) (hw : ∀ C₀,0 ≤ w C₀ ∧ w C₀ ≤ B)
    (Y : Finset V) (E : Finset (V×V)) (hE : ∀ e∈E,e.1≠e.2) (v : V) (d : ℕ)
    (hd : (E.filter (fun e => v=e.1 ∨ v=e.2)).card ≤ d) (hsize : E.card ≤ Y.card) :
    0 ≤ hypergraphWeightedDegree R (inducedResourceWeight R w Y) v-
      hypergraphWeightedDegree R (pairRestrictedResourceWeight R (inducedResourceWeight R w Y) E) v ∧
    hypergraphWeightedDegree R (inducedResourceWeight R w Y) v-
      hypergraphWeightedDegree R (pairRestrictedResourceWeight R (inducedResourceWeight R w Y) E) v ≤
      ((d:ℝ)+1)*(J:ℝ)*(Y.card:ℝ)^(c-2)*B := by
  obtain ⟨h₀,h₁⟩ := resource_forbidden_pairs_degree_loss R c J hc hR hJ w B hB hw Y E hE v
  have hd' : ((E.filter (fun e => v=e.1 ∨ v=e.2)).card:ℝ) ≤ d := by exact_mod_cast hd
  have he' : ((E.filter (fun e => ¬(v=e.1 ∨ v=e.2))).card:ℝ) ≤ Y.card := by
    exact_mod_cast ((Finset.card_filter_le _ _).trans hsize : (E.filter (fun e => ¬(v=e.1 ∨ v=e.2))).card ≤ Y.card)
  have he : (Y.card:ℝ)*(Y.card:ℝ)^(c-3)=(Y.card:ℝ)^(c-2) := by
    rw [← pow_succ'];congr 1;omega
  refine ⟨h₀,h₁.trans ?_⟩
  calc
    _ ≤ (d:ℝ)*((J:ℝ)*(Y.card:ℝ)^(c-2)*B)+(Y.card:ℝ)*((J:ℝ)*(Y.card:ℝ)^(c-3)*B) :=
      add_le_add (mul_le_mul_of_nonneg_right hd' (by positivity)) (mul_le_mul_of_nonneg_right he' (by positivity))
    _ = _ := by rw [← he];ring

end Oberwolfach
