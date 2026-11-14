module

public import Oberwolfach.IsolatorConfigurationCounts
public import Oberwolfach.OrdinaryRimPairCodegrees

@[expose] public section

/-! Upper counts for any injectively represented family of k-sets with two
prescribed vertices. These count physical sets, without ordering multiplicities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] {k : ℕ}

theorem fixedSetFamily_root_count (S : I → FixedSubset V k) (hinj : Function.Injective S)
    (R : Finset V) (hR : R.card≤k) :
    (∑ i,if R⊆(S i).val then (1:ℝ) else 0)≤(Fintype.card V:ℝ)^(k-R.card) := by
  let A := {i : I // R⊆(S i).val}
  let B := {T : FixedSubset V k // R⊆T.val}
  let f (i : A) : B := ⟨S i.val,i.property⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    exact hinj (congrArg Subtype.val hij)
  have hc : Fintype.card A≤Fintype.card V^(k-R.card) := by
    calc
      _ ≤ Fintype.card B := Fintype.card_le_of_injective f hf
      _ = (Fintype.card V-R.card).choose (k-R.card) := by
        simpa only [← Nat.card_eq_fintype_card] using fixedSubset_containing_card R hR
      _ ≤ (Fintype.card V-R.card)^(k-R.card) := Nat.choose_le_pow _ _
      _ ≤ _ := Nat.pow_le_pow_left (Nat.sub_le _ _) _
  have he : (∑ i,if R⊆(S i).val then (1:ℝ) else 0)=(Fintype.card A:ℝ) := by
    simp only [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one,Fintype.card_subtype,A]
  rw [he]
  exact_mod_cast hc


theorem fixedSetFamily_total (S : I → FixedSubset V k) (hinj : Function.Injective S)
    (x y : V) (hxy : x≠y) (hk : 2≤k)
    (hroot : ∀ i,x∈(S i).val ∧ y∈(S i).val) :
    (Fintype.card I:ℝ)≤(Fintype.card V:ℝ)^(k-2) := by
  have hc : ({x,y}:Finset V).card=2 := by simp [hxy]
  have hh := fixedSetFamily_root_count S hinj {x,y} (by simpa only [hc] using hk)
  have he (i : I) : ({x,y}:Finset V)⊆(S i).val := by
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using hroot i
  simpa only [he,ite_true,Finset.sum_const,nsmul_eq_mul,mul_one,Finset.card_univ,hc] using hh


theorem fixedSetFamily_distinct_edge_count (S : I → FixedSubset V k) (hinj : Function.Injective S)
    (x y : V) (hxy : x≠y) (hk : 4≤k) (hn : 0<Fintype.card V)
    (hroot : ∀ i,x∈(S i).val ∧ y∈(S i).val)
    (z t : V) (hzt : z≠t) (he : s(x,y)≠s(z,t)) :
    (∑ i,if z∈(S i).val ∧ t∈(S i).val then (1:ℝ) else 0)≤
      (Fintype.card V:ℝ)^(k-3) := by
  have hc := distinct_pair_union_card x y z t hxy hzt he
  have hh := fixedSetFamily_root_count S hinj {x,y,z,t} (hc.2.trans hk)
  have hpred (i : I) : (({x,y,z,t}:Finset V)⊆(S i).val)↔(z∈(S i).val ∧ t∈(S i).val) := by
    simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff,(hroot i).1,(hroot i).2,true_and]
  simp only [hpred] at hh
  exact hh.trans (pow_le_pow_right₀ (by exact_mod_cast hn : (1:ℝ)≤Fintype.card V)
    (Nat.sub_le_sub_left hc.1 k))

end Oberwolfach
