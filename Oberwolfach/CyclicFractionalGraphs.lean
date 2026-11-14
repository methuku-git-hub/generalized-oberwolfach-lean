module

public import Oberwolfach.CyclicGraphs
public import Oberwolfach.CyclicInterfaceFractional

@[expose] public section

/-! Edge equations for embedded cycles, including zero loads on nonedges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finRotate_ne_self {k : ℕ} (i : Fin (k + 2)) :
    finRotate (k + 2) i ≠ i := by
  intro h
  rw [finRotate_apply] at h
  have h1 : (1 : Fin (k + 2)) = 0 := add_left_cancel (show i + 1 = i + 0 by simpa using h)
  have hv := congrArg Fin.val h1
  norm_num at hv

theorem positive_weight_has_positive_marginal {Ω E : Type*} [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ a, 0 ≤ w a) (f : Ω → E) (a : Ω) (ha : 0 < w a) :
    0 < ∑ b, if f b = f a then w b else 0 := by
  have hle : w a ≤ ∑ b, if f b = f a then w b else 0 := by
    have hh := Finset.single_le_sum
      (f := fun b => if f b = f a then w b else 0)
      (s := Finset.univ) (a := a)
      (fun b _ => by split_ifs; exact hw b; exact le_refl _) (Finset.mem_univ a)
    simpa only [ite_true] using hh
  exact lt_of_lt_of_le ha hle

set_option maxHeartbeats 800000 in
theorem cyclic_weighting_graph_equations {k : ℕ} {X Y : Type*}
    [Fintype X] [Fintype Y]
    (L : Fin (k + 2) → X → Y → Prop) (R : Fin (k + 2) → Y → X → Prop)
    (ω : (Fin (k + 2) → X × Y × X) → ℝ)
    (hω : ∀ p, 0 ≤ ω p)
    (hleft : ∀ i x y, (∑ p, if ((p i).1, (p i).2.1) = (x, y) then ω p else 0) =
      interfaceCapacity (L i) x y)
    (hright : ∀ i y z, (∑ p, if ((p i).2.1, (p i).2.2) = (y, z) then ω p else 0) =
      interfaceCapacity (R i) y z)
    (hclosed : ∀ p, 0 < ω p → ∀ i, (p i).2.2 = (p (finRotate (k + 2) i)).1) :
    (∀ p, 0 < ω p → alternatingTupleGraph p ≤ cyclicInterfaceGraph L R) ∧
    (∀ u v, (∑ p, if (alternatingTupleGraph p).Adj u v then ω p else 0) =
      if (cyclicInterfaceGraph L R).Adj u v then (1 : ℝ) else 0) := by
  have hsupp (p : Fin (k + 2) → X × Y × X) (hp : 0 < ω p) :
      (∀ i, L i (p i).1 (p i).2.1) ∧ (∀ i, R i (p i).2.1 (p i).2.2) := by
    constructor <;> intro i
    · have hh := positive_weight_has_positive_marginal ω hω
        (fun p => ((p i).1, (p i).2.1)) p hp
      have he := hleft i (p i).1 (p i).2.1
      simp only [Prod.mk.injEq] at hh he
      rw [he] at hh
      by_contra h
      simp [interfaceCapacity, h] at hh
    · have hh := positive_weight_has_positive_marginal ω hω
        (fun p => ((p i).2.1, (p i).2.2)) p hp
      have he := hright i (p i).2.1 (p i).2.2
      simp only [Prod.mk.injEq] at hh he
      rw [he] at hh
      by_contra h
      simp [interfaceCapacity, h] at hh
  refine ⟨fun p hp => alternatingTupleGraph_le L R p (hsupp p hp).1
    (hsupp p hp).2 (hclosed p hp), ?_⟩
  have hcross (i j : Fin (k + 2)) (x : X) (y : Y) :
      (∑ p, if (alternatingTupleGraph p).Adj (Sum.inl (i, x)) (Sum.inr (j, y)) then ω p else 0) =
      if (cyclicInterfaceGraph L R).Adj (Sum.inl (i, x)) (Sum.inr (j, y)) then 1 else 0 := by
    by_cases hij : i = j
    · subst j
      have hne : i ≠ finRotate (k + 2) i := (finRotate_ne_self i).symm
      simpa only [alternatingTupleGraph_adj_cross, cyclicInterfaceGraph,
        eq_self_iff_true, true_or, true_and, hne, false_and, or_false,
        ← Prod.mk.injEq, interfaceCapacity] using hleft i x y
    · by_cases hnext : i = finRotate (k + 2) j
      · have heq (p : Fin (k + 2) → X × Y × X) :
          (if (alternatingTupleGraph p).Adj (Sum.inl (i, x)) (Sum.inr (j, y))
            then ω p else 0) =
          if ((p j).2.1, (p j).2.2) = (y, x) then ω p else 0 := by
          by_cases hz : ω p = 0
          · simp [hz]
          · have hp := lt_of_le_of_ne (hω p) (Ne.symm hz)
            have hc := hclosed p hp j
            simp only [alternatingTupleGraph_adj_cross, hnext, or_true,
              true_and, Prod.mk.injEq]
            simp only [← hc, and_comm]
        simp_rw [heq]
        rw [hright]
        simp [cyclicInterfaceGraph, hnext, finRotate_ne_self j, interfaceCapacity]
      · simp only [alternatingTupleGraph_adj_cross, cyclicInterfaceGraph,
          hij, hnext, false_or, false_and, ite_false, Finset.sum_const_zero]
  intro u v
  cases u with
  | inl u =>
    cases v with
    | inl v =>
      simp only [(alternatingTupleGraph_no_same _).1 u v, ite_false,
        Finset.sum_const_zero, cyclicInterfaceGraph]
    | inr v => exact hcross u.1 v.1 u.2 v.2
  | inr u =>
    cases v with
    | inl v =>
      simpa only [SimpleGraph.adj_comm] using hcross v.1 u.1 v.2 u.2
    | inr v =>
      simp only [(alternatingTupleGraph_no_same _).2 u v, ite_false,
        Finset.sum_const_zero, cyclicInterfaceGraph]

end Oberwolfach
