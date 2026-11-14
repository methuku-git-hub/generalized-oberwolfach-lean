module

public import Oberwolfach.AbsorberFamilyCounts

@[expose] public section

/-! Actual signed averages over an arbitrary allowed family of labelled
absorbers. The denominator is the number of records, not the number of
unlabelled vertex sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C T : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] [Fintype T] {c : ℕ}

def labelledFamilyTrade (R : C → Finset V) (S : T → VertexAbsorberTemplate c)
    (X : Finset V) (A : Finset (LabelledAbsorberFamily R S X)) (C₀ : C) : ℝ :=
  finiteSignedAverage (fun D : A => absorberTrade
    (labelledAbsorberZero R (S D.val.1) X D.val.2)
    (labelledAbsorberOne R (S D.val.1) X D.val.2)) C₀

theorem labelled_family_trade_incidence (R : C → Finset V) (S : T → VertexAbsorberTemplate c)
    (X : Finset V) (A : Finset (LabelledAbsorberFamily R S X)) (hA : A.Nonempty) (v : V) :
    (∑ C₀,if v∈R C₀ then labelledFamilyTrade R S X A C₀ else 0)=if v∈X then 1 else 0 := by
  have hh := finiteSignedAverage_indicator_constant (I:=A)
    (by simpa only [Fintype.card_coe] using Finset.card_pos.mpr hA)
    (fun D : A => absorberTrade (labelledAbsorberZero R (S D.val.1) X D.val.2)
      (labelledAbsorberOne R (S D.val.1) X D.val.2))
    (fun C₀ => v∈R C₀) (if v∈X then (1:ℝ) else 0)
    (by intro D;convert labelled_absorber_trade_incidence R (S D.val.1) X D.val.2 v using 1 <;> congr!)
  convert hh using 1 <;> congr!

theorem labelled_family_trade_bound (R : C → Finset V) (S : T → VertexAbsorberTemplate c)
    (X : Finset V) (A : Finset (LabelledAbsorberFamily R S X)) (C₀ : C) :
    |labelledFamilyTrade R S X A C₀| ≤
      (Fintype.card {D : A // ∃ o,(D.val.2.2 o).val=C₀}:ℝ)/A.card := by
  apply (finiteSignedAverage_abs_le _ C₀).trans
  rw [Fintype.card_coe]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ D : A,(if ∃ o,(D.val.2.2 o).val=C₀ then (1:ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro D _
      by_cases ho : ∃ o,(D.val.2.2 o).val=C₀
      · simp only [ho,ite_true]
        unfold absorberTrade
        split_ifs <;> norm_num
      · have hz : C₀∉labelledAbsorberZero R (S D.val.1) X D.val.2 := by
          intro hm
          obtain ⟨i,_,he⟩ := Finset.mem_image.mp hm
          exact ho ⟨Sum.inl i,he⟩
        have h₁ : C₀∉labelledAbsorberOne R (S D.val.1) X D.val.2 := by
          intro hm
          obtain ⟨i,_,he⟩ := Finset.mem_image.mp hm
          exact ho ⟨Sum.inr i,he⟩
        simp only [ho,hz,h₁,absorberTrade,ite_false,sub_self,abs_zero,le_refl]
    _ = _ := by simp only [Fintype.card_subtype,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

end Oberwolfach
