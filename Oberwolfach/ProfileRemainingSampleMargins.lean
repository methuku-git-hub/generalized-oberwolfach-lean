module

public import Oberwolfach.ProfileRestrictionCounts

@[expose] public section

/-! Explicit population margins after removing a fixed forbidden set.
The ambient multiplier is real; all actual class sizes remain integers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]

theorem profile_remaining_class_lower (a : I → ℕ) (k F : ℝ)
    (hn : ∀ i,(Fintype.card (V i):ℝ)=a i*k) (Z : Finset (Σ i,V i))
    (hZ : (Z.card:ℝ) ≤ F) (i : I) :
    (a i:ℝ)*k-F ≤ Fintype.card (ProfileRemainingClass Z i) := by
  let z := (Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈Z)).card
  have hzN : z ≤ Fintype.card (V i) := Finset.card_le_univ _
  have hzZ : z ≤ Z.card := by
    rw [show z=(Z.filter (fun v => v.1=i)).card from (sigma_finset_class_card Z i).symm]
    exact Finset.card_filter_le _ _
  have hzR : (z:ℝ) ≤ F := (by exact_mod_cast hzZ : (z:ℝ) ≤ Z.card).trans hZ
  rw [profileRemainingClass_card,Nat.cast_sub hzN,hn]
  change (a i:ℝ)*k-F ≤ (a i:ℝ)*k-z
  linarith

theorem profile_remaining_class_half (a : I → ℕ) (ha : ∀ i,1 ≤ a i) (k F : ℝ)
    (hk : 0 < k) (hF : 2*F ≤ k)
    (hn : ∀ i,(Fintype.card (V i):ℝ)=a i*k) (Z : Finset (Σ i,V i))
    (hZ : (Z.card:ℝ) ≤ F) (i : I) :
    (a i:ℝ)*k/2 ≤ Fintype.card (ProfileRemainingClass Z i) := by
  have hlow := profile_remaining_class_lower a k F hn Z hZ i
  have hai : (1:ℝ) ≤ a i := by exact_mod_cast ha i
  nlinarith

theorem profile_remaining_sampling_ratio (a : I → ℕ) (ha : ∀ i,1 ≤ a i) (k F t : ℝ)
    (hk : 0 < k) (ht : 0 ≤ t) (hF : 2*F ≤ k)
    (hn : ∀ i,(Fintype.card (V i):ℝ)=a i*k) (Z : Finset (Σ i,V i))
    (hZ : (Z.card:ℝ) ≤ F) (m : I → ℕ) (hm : ∀ i,(m i:ℝ) ≤ a i*t) (i : I) :
    (m i:ℝ)/Fintype.card (ProfileRemainingClass Z i) ≤ 2*t/k := by
  have hl := profile_remaining_class_half a ha k F hk hF hn Z hZ i
  have hai : (0:ℝ) < a i := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (ha i))
  have hd : 0 < (a i:ℝ)*k/2 := by positivity
  have hnpos := hd.trans_le hl
  calc
    _ ≤ ((a i:ℝ)*t)/Fintype.card (ProfileRemainingClass Z i) := div_le_div_of_nonneg_right (hm i) hnpos.le
    _ ≤ ((a i:ℝ)*t)/((a i:ℝ)*k/2) := div_le_div_of_nonneg_left (by positivity) hd hl
    _ = _ := by field_simp

theorem profile_remaining_sample_feasible (a : I → ℕ) (ha : ∀ i,1 ≤ a i) (k F : ℝ) (t : ℕ)
    (hk : 0 < k) (ht : (2:ℝ)*t ≤ k) (hF : 2*F ≤ k)
    (hn : ∀ i,(Fintype.card (V i):ℝ)=a i*k) (Z : Finset (Σ i,V i))
    (hZ : (Z.card:ℝ) ≤ F) (i : I) : a i*t ≤ Fintype.card (ProfileRemainingClass Z i) := by
  have hl := profile_remaining_class_half a ha k F hk hF hn Z hZ i
  have hai : (0:ℝ) ≤ a i := by positivity
  have hh : (a i:ℝ)*t ≤ Fintype.card (ProfileRemainingClass Z i) := by nlinarith
  exact_mod_cast hh

end Oberwolfach
