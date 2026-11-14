module

public import Oberwolfach.MarkedWheelFamilyLoads

@[expose] public section

/-! Separate forced attachment occurrences from the freely selected row
occurrences. Only the latter are capped by the greedy saturation rule. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K I : Type} [Fintype V] [Fintype U] [Fintype I] [DecidableEq V] [DecidableEq U]
    {tail head : E → V} {ktail khead : K → V} {H₀ HK : V → U → Prop}
    {π : Equiv.Perm V} {b m : ℕ}

def markedFamilyFreeRowLoad (C : I → MarkedWheel tail head ktail khead m π b H₀ HK)
    (a z : I → V) (v : V) : ℕ :=
  (Finset.univ.filter (fun i => v∈markedWheelRows (C i) ∧ v≠a i ∧ v≠z i)).card

theorem markedFamilyFreeRowLoad_le (C : I → MarkedWheel tail head ktail khead m π b H₀ HK)
    (a z : I → V) (v : V) : markedFamilyFreeRowLoad C a z v≤markedFamilyRowLoad C v := by
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2.1⟩

theorem markedFamilyFreeRowLoad_total (C : I → MarkedWheel tail head ktail khead m π b H₀ HK)
    (a z : I → V) : ∑ v, markedFamilyFreeRowLoad C a z v≤Fintype.card I*(m+1) := by
  exact (Finset.sum_le_sum (fun v _ => markedFamilyFreeRowLoad_le C a z v)).trans
    (markedFamilyRowLoad_total C).le

theorem markedFamilyFreeRowLoad_saturated (C : I → MarkedWheel tail head ktail khead m π b H₀ HK)
    (a z : I → V) (K : ℕ) :
    K*(Finset.univ.filter (fun v => K≤markedFamilyFreeRowLoad C a z v)).card≤Fintype.card I*(m+1) := by
  calc
    _ = ∑ v∈Finset.univ.filter (fun v => K≤markedFamilyFreeRowLoad C a z v),K := by simp [Nat.mul_comm]
    _ ≤ ∑ v∈Finset.univ.filter (fun v => K≤markedFamilyFreeRowLoad C a z v),markedFamilyFreeRowLoad C a z v :=
      Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2)
    _ ≤ ∑ v,markedFamilyFreeRowLoad C a z v := Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
    _ ≤ _ := markedFamilyFreeRowLoad_total C a z

theorem markedFamilyRowLoad_le_free_add_forced
    (C : I → MarkedWheel tail head ktail khead m π b H₀ HK) (a z : I → V) (v : V) :
    markedFamilyRowLoad C v≤markedFamilyFreeRowLoad C a z v+
      (Finset.univ.filter (fun i => v=a i ∨ v=z i)).card := by
  have hs : Finset.univ.filter (fun i => v∈markedWheelRows (C i)) ⊆
      Finset.univ.filter (fun i => v∈markedWheelRows (C i) ∧ v≠a i ∧ v≠z i) ∪
      Finset.univ.filter (fun i => v=a i ∨ v=z i) := by
    intro i hi
    by_cases h : v=a i ∨ v=z i
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2,fun ha => h (Or.inl ha),fun hz => h (Or.inr hz)⟩)
  exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)

theorem markedFamilyFreeRowLoad_snoc {n : ℕ}
    (C : Fin n → MarkedWheel tail head ktail khead m π b H₀ HK)
    (a z : Fin n → V) (D : MarkedWheel tail head ktail khead m π b H₀ HK) (a' z' v : V) :
    markedFamilyFreeRowLoad (Fin.snoc C D) (Fin.snoc a a') (Fin.snoc z z') v=
      markedFamilyFreeRowLoad C a z v+(if v∈markedWheelRows D ∧ v≠a' ∧ v≠z' then 1 else 0) := by
  simp only [markedFamilyFreeRowLoad,Finset.card_filter]
  rw [Fin.sum_univ_castSucc]
  have hc (i : Fin n) := @Fin.snoc_castSucc n
    (fun _ => MarkedWheel tail head ktail khead m π b H₀ HK) D C i
  have hl := @Fin.snoc_last n
    (fun _ => MarkedWheel tail head ktail khead m π b H₀ HK) D C
  apply congrArg₂ (·+·)
  · apply Finset.sum_congr rfl
    intro i hi
    rw [hc,Fin.snoc_castSucc,Fin.snoc_castSucc]
  · rw [hl,Fin.snoc_last,Fin.snoc_last]

theorem marked_free_rim_degree
    (C : I → MarkedWheel tail head ktail khead m π b H₀ HK) (a z : I → V)
    (hb : 1≤b) (X : Finset V) (hX : ∀ v, π v∈X ↔ v∈X)
    (K D : ℕ) (hfree : ∀ v∈X, markedFamilyFreeRowLoad C a z v≤K)
    (hforced : ∀ v, (Finset.univ.filter (fun i => v=a i ∨ v=z i)).card≤D) :
    ∀ v, (spanningRestriction (markedFamilyRim C) X).degree v≤4*(K+D) := by
  intro v
  rw [spanningRestriction_degree]
  by_cases hv : v∈X
  · rw [if_pos hv]
    have hprev : π.symm v∈X := (hX (π.symm v)).mp (by simpa using hv)
    have hvload := (markedFamilyRowLoad_le_free_add_forced C a z v).trans
      (Nat.add_le_add (hfree v hv) (hforced v))
    have hpload := (markedFamilyRowLoad_le_free_add_forced C a z (π.symm v)).trans
      (Nat.add_le_add (hfree _ hprev) (hforced _))
    have hh := (Finset.card_le_card (Finset.inter_subset_left : (markedFamilyRim C).neighborFinset v∩X⊆_)).trans
      (by simpa using markedFamilyRim_degree hb C v)
    omega
  · rw [if_neg hv]; omega

end Oberwolfach
