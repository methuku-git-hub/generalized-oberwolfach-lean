module

public import Oberwolfach.NestedProfileConditioning
public import Oberwolfach.NormalizedProfileMargins

@[expose] public section

/-! Explicit inclusion-ratio errors for the actual populations after
fixed deletion and root conditioning. The ambient scale may be real. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]

theorem conditioned_profile_inclusion_ratio
    (a : I → ℕ) (ha : ∀ i,1 ≤ a i) (k F₀ : ℝ) (hk : 0 < k)
    (hn : ∀ i,(Fintype.card (V i):ℝ)=a i*k)
    (F : Finset (Σ i,V i)) (hF : (F.card:ℝ) ≤ F₀)
    (T : ∀ i,Finset (ProfileRemainingClass F i)) (P t : ℕ)
    (hT : ∀ i,(T i).card ≤ P) (r : I → ℕ) (H : ℕ) (hH : ∑ i,r i=H)
    (hHpos : 1 ≤ H) (ht : P+H ≤ t)
    (hlarge : 2*(H:ℝ)*(F₀+P+H) ≤ k) :
    |(k/(t:ℝ))^H*(∏ i,((a i*t-(T i).card).choose (r i):ℝ)/
      (Fintype.card {v : ProfileRemainingClass F i // v∉T i}).choose (r i))-1| ≤
      2*(H:ℝ)*(((P:ℝ)+H)/t+(F₀+P+H)/k) := by
  let f := fun i => (Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈F)).card
  let b := fun i => ((T i).card:ℝ)
  let d := fun i => (f i:ℝ)+(T i).card
  let m := fun i => a i*t-(T i).card
  let n := fun i => Fintype.card {v : ProfileRemainingClass F i // v∉T i}
  have hF₀ : 0 ≤ F₀ := (Nat.cast_nonneg _).trans hF
  have hHposR : (1:ℝ) ≤ H := by exact_mod_cast hHpos
  have htpos : (0:ℝ)<t := by exact_mod_cast (show 0<t by omega)
  have htR : (P:ℝ)+H ≤ t := by exact_mod_cast ht
  have haR (i) : (1:ℝ) ≤ a i := by exact_mod_cast ha i
  have hTm (i) : (T i).card ≤ a i*t := by
    have hh : t ≤ a i*t := by simpa only [one_mul] using Nat.mul_le_mul_right t (ha i)
    exact (hT i).trans ((by omega : P≤t).trans hh)
  have hf (i) : (f i:ℝ) ≤ F₀ := by
    have hh : f i ≤ F.card := by
      rw [show f i=(F.filter (fun v => v.1=i)).card from (sigma_finset_class_card F i).symm]
      exact Finset.card_filter_le _ _
    exact (by exact_mod_cast hh : (f i:ℝ) ≤ F.card).trans hF
  have hbP (i) : b i ≤ P := by dsimp [b];exact_mod_cast hT i
  have hdQ (i) : d i ≤ F₀+P := by dsimp [d];linarith [hf i,hbP i]
  have hm (i) : (m i:ℝ)=(a i:ℝ)*t-b i := by dsimp [m,b];rw [Nat.cast_sub (hTm i),Nat.cast_mul]
  have hn' (i) : (n i:ℝ)=(a i:ℝ)*k-d i := by
    have hc : n i=Fintype.card (ProfileRemainingClass F i)-(T i).card := by
      dsimp [n]
      rw [Fintype.card_subtype_compl,Fintype.card_coe]
    have hTi : (T i).card ≤ Fintype.card (ProfileRemainingClass F i) := Finset.card_le_univ _
    have hfi : f i ≤ Fintype.card (V i) := Finset.card_le_univ _
    rw [hc,Nat.cast_sub hTi,profileRemainingClass_card,Nat.cast_sub hfi,hn]
    dsimp [d,f]
    ring
  have hr (i) : r i ≤ H := by
    have hh := Finset.single_le_sum (s:=Finset.univ) (f:=r) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    simpa only [hH] using hh
  have hrm (i) : r i ≤ m i := by
    have hmH : (H:ℝ) ≤ m i := by rw [hm];nlinarith [haR i,hbP i]
    exact (hr i).trans (by exact_mod_cast hmH)
  have hrn (i) : r i ≤ n i := by
    have hkH : F₀+P+H ≤ k := by nlinarith [show (0:ℝ) ≤ F₀+P+H by positivity]
    have hnH : (H:ℝ) ≤ n i := by rw [hn'];nlinarith [haR i,hdQ i]
    exact (hr i).trans (by exact_mod_cast hnH)
  exact normalized_profile_inclusion_error_uniform (fun i => (a i:ℝ)) b d haR
    (fun i => by dsimp [b];positivity) (fun i => by dsimp [d];positivity)
    P (F₀+P) (by positivity) (by positivity) hbP hdQ t k htpos hk m n r H hH hm hn' hrm hrn hlarge

end Oberwolfach
