module

public import Mathlib.Tactic

@[expose] public section

/-! Fixed-weight resource sums with the root coordinate omitted. The
comparison is deterministic and includes roots absent from either state. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A]

def resourceRootOmittedLoad (R : I → Finset A) (w : I → ℝ) (keep : A → Prop) (e : A) : ℝ :=
  ∑ i,if e∈R i ∧ (∀ f∈R i,f≠e → keep f) then w i else 0

def resourceOmittedPairWeight (R : I → Finset A) (w : I → ℝ) (e f : A) : ℝ :=
  ∑ i,if e∈R i ∧ f∈R i ∧ f≠e then w i else 0

theorem root_omitted_indicator_change (R : I → Finset A) (w : I → ℝ)
    (hw : ∀ i,0≤w i) (keep keep' : A → Prop) (e : A) (i : I) :
    |(if e∈R i ∧ (∀ f∈R i,f≠e → keep' f) then w i else 0)-
      (if e∈R i ∧ (∀ f∈R i,f≠e → keep f) then w i else 0)|≤
    ∑ f,if ¬(keep f↔keep' f) ∧ e∈R i ∧ f∈R i ∧ f≠e then w i else 0 := by
  have hnon : 0≤∑ f,if ¬(keep f↔keep' f) ∧ e∈R i ∧ f∈R i ∧ f≠e then w i else 0 :=
    Finset.sum_nonneg (fun f _=>by split_ifs <;> first | exact hw i | rfl)
  by_cases he : e∈R i
  swap
  · simpa only [he,false_and,ite_false,sub_self,abs_zero] using hnon
  have hcost (f : A) (hf : f∈R i) (hne : f≠e) (hchange : ¬(keep f↔keep' f)) :
      w i≤∑ f,if ¬(keep f↔keep' f) ∧ e∈R i ∧ f∈R i ∧ f≠e then w i else 0 := by
    have hh := Finset.single_le_sum (s:=Finset.univ)
      (f:=fun f=>if ¬(keep f↔keep' f) ∧ e∈R i ∧ f∈R i ∧ f≠e then w i else 0)
      (fun f _=>by split_ifs <;> first | exact hw i | rfl) (Finset.mem_univ f)
    rw [if_pos ⟨hchange,he,hf,hne⟩] at hh
    exact hh
  by_cases hk : ∀ f∈R i,f≠e → keep f
  · by_cases hk' : ∀ f∈R i,f≠e → keep' f
    · rw [if_pos ⟨he,hk'⟩,if_pos ⟨he,hk⟩,sub_self,abs_zero]
      exact hnon
    · have hb := hk'
      push_neg at hb
      obtain ⟨f,hf,hne,hf'⟩ := hb
      have hh := hcost f hf hne (fun h=>hf' (h.mp (hk f hf hne)))
      rw [if_neg (fun h=>hk' h.2),if_pos ⟨he,hk⟩,zero_sub,abs_neg,abs_of_nonneg (hw i)]
      exact hh
  · by_cases hk' : ∀ f∈R i,f≠e → keep' f
    · have hb := hk
      push_neg at hb
      obtain ⟨f,hf,hne,hf'⟩ := hb
      have hh := hcost f hf hne (fun h=>hf' (h.mpr (hk' f hf hne)))
      rw [if_pos ⟨he,hk'⟩,if_neg (fun h=>hk h.2),sub_zero,abs_of_nonneg (hw i)]
      exact hh
    · rw [if_neg (fun h=>hk' h.2),if_neg (fun h=>hk h.2),sub_self,abs_zero]
      exact hnon

theorem resourceRootOmittedLoad_change (R : I → Finset A) (w : I → ℝ)
    (hw : ∀ i,0≤w i) (keep keep' : A → Prop) (e : A) :
    |resourceRootOmittedLoad R w keep' e-resourceRootOmittedLoad R w keep e|≤
      ∑ f,if ¬(keep f↔keep' f) then resourceOmittedPairWeight R w e f else 0 := by
  unfold resourceRootOmittedLoad
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i,|(if e∈R i ∧ (∀ f∈R i,f≠e → keep' f) then w i else 0)-
      (if e∈R i ∧ (∀ f∈R i,f≠e → keep f) then w i else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i,∑ f,if ¬(keep f↔keep' f) ∧ e∈R i ∧ f∈R i ∧ f≠e then w i else 0 :=
      Finset.sum_le_sum (fun i _=>root_omitted_indicator_change R w hw keep keep' e i)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro f _
      by_cases hf : keep f↔keep' f
      · simp only [hf,not_true_eq_false,false_and,ite_false,Finset.sum_const_zero]
      · simp only [hf,not_false_eq_true,true_and,ite_true,resourceOmittedPairWeight]

theorem resourceRootOmittedLoad_present (R : I → Finset A) (w : I → ℝ)
    (keep : A → Prop) (e : A) (he : keep e) :
    resourceRootOmittedLoad R w keep e=∑ i,if e∈R i ∧ (∀ f∈R i,keep f) then w i else 0 := by
  unfold resourceRootOmittedLoad
  apply Finset.sum_congr rfl
  intro i _
  have hh : (∀ f∈R i,f≠e → keep f)↔∀ f∈R i,keep f := by
    constructor
    · intro h f hf
      by_cases hfe : f=e
      · simpa only [hfe] using he
      · exact h f hf hfe
    · intro h f hf _;exact h f hf
  by_cases h : e∈R i ∧ (∀ f∈R i,keep f)
  · rw [if_pos ⟨h.1,hh.mpr h.2⟩,if_pos h]
  · rw [if_neg (fun h'=>h ⟨h'.1,hh.mp h'.2⟩),if_neg h]

end Oberwolfach
