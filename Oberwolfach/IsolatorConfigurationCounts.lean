module

public import Oberwolfach.OrdinaryIsolatorConfigurations
public import Oberwolfach.SubsetCounts
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

/-! At a specified hub, an isolator configuration is determined by its
k-vertex set. Prescribing additional vertices gives the required power bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem isolator_configuration_hub_root_count {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    {P Q F : SimpleGraph V} {H : V → U → Prop} {k : ℕ} {θ α : ℝ} {x y : V}
    (u : U) (R : Finset V) (hR : R.card≤k) :
    (∑ T : OrdinaryIsolatorConfiguration P Q F H k θ α x y,
      if T.hub=u ∧ R⊆T.vertices.val then (1:ℝ) else 0)≤
      (Fintype.card V:ℝ)^(k-R.card) := by
  let A := {T : OrdinaryIsolatorConfiguration P Q F H k θ α x y // T.hub=u ∧ R⊆T.vertices.val}
  let B := {S : FixedSubset V k // R⊆S.val}
  let f (T : A) : B := ⟨T.val.vertices,T.property.2⟩
  have hf : Function.Injective f := by
    intro T T' he
    apply Subtype.ext
    apply OrdinaryIsolatorConfiguration.encoding_injective
    apply Prod.ext
    · exact T.property.1.trans T'.property.1.symm
    · exact congrArg Subtype.val he
  have hc : Fintype.card A≤Fintype.card V^(k-R.card) := by
    calc
      _ ≤ Fintype.card B := Fintype.card_le_of_injective f hf
      _ = (Fintype.card V-R.card).choose (k-R.card) := by
        simpa only [← Nat.card_eq_fintype_card] using fixedSubset_containing_card R hR
      _ ≤ (Fintype.card V-R.card)^(k-R.card) := Nat.choose_le_pow _ _
      _ ≤ _ := Nat.pow_le_pow_left (Nat.sub_le _ _) _
  have he : (∑ T : OrdinaryIsolatorConfiguration P Q F H k θ α x y,
      if T.hub=u ∧ R⊆T.vertices.val then (1:ℝ) else 0)=(Fintype.card A:ℝ) := by
    simp only [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one,Fintype.card_subtype,A]
  rw [he]
  exact_mod_cast hc

theorem isolator_configuration_hub_count {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    {P Q F : SimpleGraph V} {H : V → U → Prop} {k : ℕ} {θ α : ℝ} {x y : V}
    (u : U) (hxy : x≠y) (hk : 2≤k) :
    (∑ T : OrdinaryIsolatorConfiguration P Q F H k θ α x y,
      if T.hub=u then (1:ℝ) else 0)≤(Fintype.card V:ℝ)^(k-2) := by
  have hR : ({x,y}:Finset V).card=2 := by simp [hxy]
  have hh := isolator_configuration_hub_root_count (P:=P) (Q:=Q) (F:=F) (H:=H)
    (θ:=θ) (α:=α) (x:=x) (y:=y) u {x,y} (by simpa only [hR] using hk)
  rw [hR] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro T _
  have he : ({x,y}:Finset V)⊆T.vertices.val := by
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using T.endpoints
  simp only [he,and_true]

end Oberwolfach
