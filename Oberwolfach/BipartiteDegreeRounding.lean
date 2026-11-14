module

public import Oberwolfach.DemandMatchingDegrees
public import Oberwolfach.FiniteLawMap
public import Oberwolfach.CommonEvents

@[expose] public section

/-! Exact integer bipartite degrees can be sampled with any prescribed
fractional edge marginals in [0,1]. No independence assertion is made. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 800000 in
theorem bipartite_degree_rounding {X Y E : Type*}
    [Fintype X] [Fintype Y] [Fintype E] [DecidableEq E]
    (tail : E → X) (head : E → Y) (f : X → ℕ) (g : Y → ℕ) (z : E → ℝ)
    (hz : ∀ e, 0 ≤ z e ∧ z e ≤ 1)
    (hrow : ∀ x, (∑ e, if tail e = x then z e else 0) = f x)
    (hcol : ∀ y, (∑ e, if head e = y then z e else 0) = g y) :
    ∃ ν : FiniteLaw (E → Bool),
      (∀ D, 0 < ν.mass D →
        (∀ x, (∑ e, if tail e = x ∧ D e = true then (1 : ℕ) else 0) = f x) ∧
        (∀ y, (∑ e, if head e = y ∧ D e = true then (1 : ℕ) else 0) = g y)) ∧
      (∀ e, ν.probability (fun D => D e = true) = z e) := by
  classical
  let b := Fintype.equivOfCardEq (demandMatching_parts_card tail head f g z hrow hcol)
  let M := demandMatchingMatrix tail head f g z
  obtain ⟨μ, hμ⟩ := bistochastic_sampling b M (demandMatchingMatrix_nonneg tail head f g z hz)
    (demandMatchingMatrix_row tail head f g z (fun e => (hz e).1) hrow hcol)
    (demandMatchingMatrix_column tail head f g z (fun e => (hz e).1) hrow hcol)
  let σ (p : Equiv.Perm (DemandSlots f ⊕ E)) := p.trans b
  let D (p : Equiv.Perm (DemandSlots f ⊕ E)) (e : E) : Bool :=
    decide (σ p (Sum.inr e) ≠ Sum.inr e)
  have hallowed (p : Equiv.Perm (DemandSlots f ⊕ E)) (hp : 0 < μ.mass p) :
      ∀ a, DemandMatchingAllowed tail head f g a (σ p a) := by
    intro a
    apply demandMatchingMatrix_pos_allowed tail head f g z
    have hm := hμ a (b (p a))
    have hh := Finset.single_le_sum
      (f := fun q => if b (q a) = b (p a) then μ.mass q else 0)
      (s := Finset.univ) (a := p)
      (fun q _ => by split_ifs; exact μ.nonneg q; exact le_refl _) (Finset.mem_univ p)
    simp only [ite_true, hm] at hh
    exact lt_of_lt_of_le hp hh
  refine ⟨μ.map D, ?_, ?_⟩
  · intro A hA
    have hA' : 0 < ∑ p, if D p = A then μ.mass p else 0 := by
      convert hA using 1
      unfold FiniteLaw.map
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> rfl
    obtain ⟨p, _, hp⟩ := (Finset.sum_pos_iff_of_nonneg
      (fun p (_ : p ∈ Finset.univ) => show 0 ≤ (if D p = A then μ.mass p else 0) by
        split_ifs; exact μ.nonneg p; exact le_refl _)).mp hA'
    split_ifs at hp with he
    · subst A
      constructor
      · intro x
        simp only [D, decide_eq_true_eq]
        convert demandMatching_row_count tail head f g (σ p) (hallowed p hp) x using 1
        apply Finset.sum_congr rfl
        intro e _
        split_ifs <;> rfl
      · intro y
        simp only [D, decide_eq_true_eq]
        convert demandMatching_column_count tail head f g (σ p) (hallowed p hp) y using 1
        apply Finset.sum_congr rfl
        intro e _
        split_ifs <;> rfl
    · exact False.elim ((lt_irrefl 0) hp)
  · intro e
    rw [finiteLaw_map_probability]
    change μ.probability (fun p => decide (σ p (Sum.inr e) ≠ Sum.inr e) = true) = z e
    have he : μ.probability (fun p => σ p (Sum.inr e) = Sum.inr e) = 1 - z e := by
      have hh := hμ (Sum.inr e) (Sum.inr e)
      simp only [M, demandMatchingMatrix, ite_true] at hh
      unfold FiniteLaw.probability
      convert hh using 1
      apply Finset.sum_congr rfl
      intro p _
      dsimp only [σ, Equiv.trans_apply]
      split_ifs <;> rfl
    have hc := finiteLaw_probability_compl μ (fun p => σ p (Sum.inr e) = Sum.inr e)
    rw [he] at hc
    simp only [decide_eq_true_eq]
    linarith

end Oberwolfach
