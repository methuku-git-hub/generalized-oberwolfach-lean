module

public import Oberwolfach.BistochasticSampling

@[expose] public section

/-! The bounded bipartite degree problem is encoded as a bistochastic
matching problem. Each original edge has one pair of auxiliary vertices;
matching that pair means the original edge is unused. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

abbrev DemandSlots {X : Type*} (f : X → ℕ) := Σ x, Fin (f x)

def demandMatchingMatrix {X Y E : Type*}
    (tail : E → X) (head : E → Y) (f : X → ℕ) (g : Y → ℕ) (z : E → ℝ) :
    (DemandSlots f ⊕ E) → (DemandSlots g ⊕ E) → ℝ
  | Sum.inl a, Sum.inl _ => 0
  | Sum.inl a, Sum.inr e => if a.1 = tail e then z e / f (tail e) else 0
  | Sum.inr e, Sum.inl b => if head e = b.1 then z e / g (head e) else 0
  | Sum.inr e, Sum.inr e' => if e = e' then 1 - z e else 0

def DemandMatchingAllowed {X Y E : Type*}
    (tail : E → X) (head : E → Y) (f : X → ℕ) (g : Y → ℕ) :
    (DemandSlots f ⊕ E) → (DemandSlots g ⊕ E) → Prop
  | Sum.inl a, Sum.inl _ => False
  | Sum.inl a, Sum.inr e => a.1 = tail e
  | Sum.inr e, Sum.inl b => head e = b.1
  | Sum.inr e, Sum.inr e' => e = e'

theorem demandMatchingMatrix_nonneg {X Y E : Type*}
    (tail : E → X) (head : E → Y) (f : X → ℕ) (g : Y → ℕ) (z : E → ℝ)
    (hz : ∀ e, 0 ≤ z e ∧ z e ≤ 1) :
    ∀ a b, 0 ≤ demandMatchingMatrix tail head f g z a b := by
  intro a b
  cases a <;> cases b <;> simp only [demandMatchingMatrix]
  · exact le_refl _
  · split_ifs; exact div_nonneg (hz _).1 (Nat.cast_nonneg _); exact le_refl _
  · split_ifs; exact div_nonneg (hz _).1 (Nat.cast_nonneg _); exact le_refl _
  · split_ifs; exact sub_nonneg.mpr (hz _).2; exact le_refl _

theorem demandMatchingMatrix_pos_allowed {X Y E : Type*}
    (tail : E → X) (head : E → Y) (f : X → ℕ) (g : Y → ℕ) (z : E → ℝ)
    (a : DemandSlots f ⊕ E) (b : DemandSlots g ⊕ E)
    (h : 0 < demandMatchingMatrix tail head f g z a b) :
    DemandMatchingAllowed tail head f g a b := by
  cases a <;> cases b <;> simp only [demandMatchingMatrix, DemandMatchingAllowed] at h ⊢
  · exact (lt_irrefl 0) h
  all_goals split_ifs at h with hh; exact hh; exact False.elim ((lt_irrefl 0) h)

theorem sum_slots_indicator {X : Type*} [Fintype X] (f : X → ℕ) (x : X) (a : ℝ) :
    (∑ s : DemandSlots f, if x = s.1 then a else 0) = (f x : ℝ) * a := by
  classical
  rw [Fintype.sum_sigma]
  have hinner (y : X) : (∑ _i : Fin (f y), if x = y then a else 0) =
      if x = y then (f y : ℝ) * a else 0 := by
    by_cases hxy : x = y <;> simp [hxy]
  simp_rw [hinner]
  simp

theorem demand_zero_forces_edge_zero {X E : Type*} [Fintype E]
    (tail : E → X) (f : X → ℕ) (z : E → ℝ) (hz : ∀ e, 0 ≤ z e)
    (hrow : ∀ x, (∑ e, if tail e = x then z e else 0) = f x)
    (e : E) (hf : f (tail e) = 0) : z e = 0 := by
  have hle := Finset.single_le_sum
    (f := fun a => if tail a = tail e then z a else 0) (s := Finset.univ) (a := e)
    (fun a _ => by split_ifs; exact hz a; exact le_refl _) (Finset.mem_univ e)
  simp only [ite_true, hrow, hf, Nat.cast_zero] at hle
  exact le_antisymm hle (hz e)

theorem demandMatchingMatrix_row {X Y E : Type*}
    [Fintype X] [Fintype Y] [Fintype E]
    (tail : E → X) (head : E → Y) (f : X → ℕ) (g : Y → ℕ) (z : E → ℝ)
    (hz : ∀ e, 0 ≤ z e)
    (hrow : ∀ x, (∑ e, if tail e = x then z e else 0) = f x)
    (hcol : ∀ y, (∑ e, if head e = y then z e else 0) = g y)
    (a : DemandSlots f ⊕ E) : ∑ b, demandMatchingMatrix tail head f g z a b = 1 := by
  classical
  rw [Fintype.sum_sum_type]
  cases a with
  | inl a =>
    simp only [demandMatchingMatrix, Finset.sum_const_zero, zero_add]
    have hf : (0 : ℝ) < f a.1 := by exact_mod_cast Nat.zero_lt_of_lt a.2.isLt
    calc
      _ = (∑ e, if tail e = a.1 then z e else 0) / f a.1 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro e _
        by_cases he : tail e = a.1
        · simp only [he, ite_true]
        · simp only [he, Ne.symm he, ite_false, zero_div]
      _ = 1 := by rw [hrow, div_self hf.ne']
  | inr e =>
    simp only [demandMatchingMatrix]
    rw [sum_slots_indicator]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    by_cases hg : g (head e) = 0
    · rw [demand_zero_forces_edge_zero head g z hz hcol e hg]
      simp
    · rw [mul_div_cancel₀ _ (by exact_mod_cast hg)]
      ring

theorem demandMatchingMatrix_transpose {X Y E : Type*}
    (tail : E → X) (head : E → Y) (f : X → ℕ) (g : Y → ℕ) (z : E → ℝ)
    (a : DemandSlots f ⊕ E) (b : DemandSlots g ⊕ E) :
    demandMatchingMatrix tail head f g z a b = demandMatchingMatrix head tail g f z b a := by
  cases a <;> cases b <;> simp only [demandMatchingMatrix, eq_comm]
  rename_i e e'
  by_cases he : e = e'
  · subst e'; simp
  · simp [he, Ne.symm he]

theorem demandMatchingMatrix_column {X Y E : Type*}
    [Fintype X] [Fintype Y] [Fintype E]
    (tail : E → X) (head : E → Y) (f : X → ℕ) (g : Y → ℕ) (z : E → ℝ)
    (hz : ∀ e, 0 ≤ z e)
    (hrow : ∀ x, (∑ e, if tail e = x then z e else 0) = f x)
    (hcol : ∀ y, (∑ e, if head e = y then z e else 0) = g y)
    (b : DemandSlots g ⊕ E) : ∑ a, demandMatchingMatrix tail head f g z a b = 1 := by
  calc
    _ = ∑ a, demandMatchingMatrix head tail g f z b a :=
      Finset.sum_congr rfl (fun a _ => demandMatchingMatrix_transpose tail head f g z a b)
    _ = 1 := demandMatchingMatrix_row head tail g f z hz hcol hrow b

theorem demandMatching_parts_card {X Y E : Type*}
    [Fintype X] [Fintype Y] [Fintype E]
    (tail : E → X) (head : E → Y) (f : X → ℕ) (g : Y → ℕ) (z : E → ℝ)
    (hrow : ∀ x, (∑ e, if tail e = x then z e else 0) = f x)
    (hcol : ∀ y, (∑ e, if head e = y then z e else 0) = g y) :
    Fintype.card (DemandSlots f ⊕ E) = Fintype.card (DemandSlots g ⊕ E) := by
  classical
  have hf : (∑ x, (f x : ℝ)) = ∑ e, z e := by
    simp_rw [← hrow]
    rw [Finset.sum_comm]
    simp
  have hg : (∑ y, (g y : ℝ)) = ∑ e, z e := by
    simp_rw [← hcol]
    rw [Finset.sum_comm]
    simp
  have htot : ∑ x, f x = ∑ y, g y := by exact_mod_cast hf.trans hg.symm
  simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin, DemandSlots]
  rw [htot]

end Oberwolfach
