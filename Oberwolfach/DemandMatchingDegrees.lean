module

public import Oberwolfach.DemandMatchingGadget

@[expose] public section

/-! Every supported perfect matching in the auxiliary graph gives a
zero-one edge set with precisely the original integer demands. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem demandMatching_row_count {X Y E : Type*}
    [Fintype E] (tail : E → X) (head : E → Y) (f : X → ℕ) (g : Y → ℕ)
    (σ : (DemandSlots f ⊕ E) ≃ (DemandSlots g ⊕ E))
    (hσ : ∀ a, DemandMatchingAllowed tail head f g a (σ a)) (x : X) :
    (∑ e, if tail e = x ∧ σ (Sum.inr e) ≠ Sum.inr e then (1 : ℕ) else 0) = f x := by
  classical
  have hslot (a : DemandSlots f) : ∃ e, tail e = a.1 ∧ σ (Sum.inl a) = Sum.inr e := by
    have ha := hσ (Sum.inl a)
    cases he : σ (Sum.inl a) with
    | inl b => rw [he] at ha; exact False.elim ha
    | inr e =>
      rw [he] at ha
      exact ⟨e, ha.symm, rfl⟩
  choose F hF hmap using hslot
  have hused (i : Fin (f x)) : σ (Sum.inr (F ⟨x, i⟩)) ≠ Sum.inr (F ⟨x, i⟩) := by
    intro he
    have hh := σ.injective ((hmap ⟨x, i⟩).trans he.symm)
    cases hh
  let t : Fin (f x) → {e : E // tail e = x ∧ σ (Sum.inr e) ≠ Sum.inr e} :=
    fun i => ⟨F ⟨x, i⟩, hF ⟨x, i⟩, hused i⟩
  have ht : Function.Bijective t := by
    constructor
    · intro i j hij
      have hv : F ⟨x, i⟩ = F ⟨x, j⟩ := congrArg Subtype.val hij
      have hh := σ.injective ((hmap ⟨x, i⟩).trans ((congrArg Sum.inr hv).trans (hmap ⟨x, j⟩).symm))
      simpa only [Sum.inl.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] using hh
    · intro e
      cases hp : σ.symm (Sum.inr e.val) with
      | inl a =>
        have he : σ (Sum.inl a) = Sum.inr e.val := by
          rw [← hp, Equiv.apply_symm_apply]
        have ha := hσ (Sum.inl a)
        rw [he] at ha
        have hax : a.1 = x := ha.trans e.property.1
        rcases a with ⟨a, i⟩
        dsimp only at hax
        subst a
        refine ⟨i, Subtype.ext ?_⟩
        exact Sum.inr.inj ((hmap ⟨x, i⟩).symm.trans he)
      | inr a =>
        have he : σ (Sum.inr a) = Sum.inr e.val := by
          rw [← hp, Equiv.apply_symm_apply]
        have ha := hσ (Sum.inr a)
        rw [he] at ha
        change a = e.val at ha
        exact False.elim (e.property.2 (ha ▸ he))
  have hc := Fintype.card_congr (Equiv.ofBijective t ht)
  simp only [Fintype.card_fin] at hc
  rw [hc]
  simp [Fintype.card_subtype]

theorem demandMatchingAllowed_symm {X Y E : Type*}
    (tail : E → X) (head : E → Y) (f : X → ℕ) (g : Y → ℕ)
    (a : DemandSlots f ⊕ E) (b : DemandSlots g ⊕ E) :
    DemandMatchingAllowed tail head f g a b ↔ DemandMatchingAllowed head tail g f b a := by
  cases a <;> cases b <;> simp only [DemandMatchingAllowed, eq_comm]

theorem demandMatching_column_count {X Y E : Type*}
    [Fintype E] (tail : E → X) (head : E → Y) (f : X → ℕ) (g : Y → ℕ)
    (σ : (DemandSlots f ⊕ E) ≃ (DemandSlots g ⊕ E))
    (hσ : ∀ a, DemandMatchingAllowed tail head f g a (σ a)) (y : Y) :
    (∑ e, if head e = y ∧ σ (Sum.inr e) ≠ Sum.inr e then (1 : ℕ) else 0) = g y := by
  have hsym (b) : DemandMatchingAllowed head tail g f b (σ.symm b) := by
    have hh := hσ (σ.symm b)
    rw [Equiv.apply_symm_apply] at hh
    exact (demandMatchingAllowed_symm tail head f g _ _).mp hh
  have hh := demandMatching_row_count head tail g f σ.symm hsym y
  convert hh using 1
  apply Finset.sum_congr rfl
  intro e _
  have he : σ (Sum.inr e) = Sum.inr e ↔ σ.symm (Sum.inr e) = Sum.inr e := by
    rw [Equiv.apply_eq_iff_eq_symm_apply]
    exact eq_comm
  by_cases hl : head e = y ∧ σ (Sum.inr e) ≠ Sum.inr e
  · have hr : head e = y ∧ σ.symm (Sum.inr e) ≠ Sum.inr e :=
      ⟨hl.1, (not_congr he).mp hl.2⟩
    rw [if_pos hl, if_pos hr]
  · have hr : ¬ (head e = y ∧ σ.symm (Sum.inr e) ≠ Sum.inr e) :=
      fun hr => hl ⟨hr.1, (not_congr he).mpr hr.2⟩
    rw [if_neg hl, if_neg hr]

end Oberwolfach
