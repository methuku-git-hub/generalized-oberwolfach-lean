module

public import Oberwolfach.AlternatingCycle

@[expose] public section

/-! The graph and its part-respecting cycle copies use disjoint tagged
vertex classes. No identification of auxiliary endpoints is implicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def cyclicInterfaceGraph {k : ℕ} {X Y : Type*}
    (L : Fin (k + 2) → X → Y → Prop) (R : Fin (k + 2) → Y → X → Prop) :
    SimpleGraph ((Fin (k + 2) × X) ⊕ (Fin (k + 2) × Y)) where
  Adj a b := match a, b with
    | Sum.inl (i, x), Sum.inr (j, y) =>
        (i = j ∧ L i x y) ∨ (i = finRotate (k + 2) j ∧ R j y x)
    | Sum.inr (j, y), Sum.inl (i, x) =>
        (i = j ∧ L i x y) ∨ (i = finRotate (k + 2) j ∧ R j y x)
    | _, _ => False
  symm := ⟨by intro a b; cases a <;> cases b <;> exact id⟩
  loopless := ⟨by intro a; cases a <;> exact id⟩

def alternatingTupleGraph {k : ℕ} {X Y : Type*}
    (p : Fin (k + 2) → X × Y × X) :
    SimpleGraph ((Fin (k + 2) × X) ⊕ (Fin (k + 2) × Y)) :=
  (SimpleGraph.cycleGraph ((k + 2) * 2)).map (alternatingCycleEmbedding p)

theorem alternatingTupleGraph_adj_cross {k : ℕ} {X Y : Type*}
    (p : Fin (k + 2) → X × Y × X) (i j : Fin (k + 2)) (x : X) (y : Y) :
    (alternatingTupleGraph p).Adj (Sum.inl (i, x)) (Sum.inr (j, y)) ↔
      (i = j ∨ i = finRotate (k + 2) j) ∧ (p i).1 = x ∧ (p j).2.1 = y := by
  rw [alternatingTupleGraph, SimpleGraph.map_adj]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    obtain ⟨⟨ia, ba⟩, rfl⟩ := finProdFinEquiv.surjective a
    obtain ⟨⟨ib, bb⟩, rfl⟩ := finProdFinEquiv.surjective b
    change alternatingCycleEmbedding p (alternatingIndex ia ba) = _ at ha
    change alternatingCycleEmbedding p (alternatingIndex ib bb) = _ at hb
    rw [alternatingCycleEmbedding_apply] at ha hb
    fin_cases ba <;> fin_cases bb <;> simp [alternatingVertex] at ha hb
    rcases ha with ⟨rfl, hx⟩
    rcases hb with ⟨rfl, hy⟩
    have hh : ia = ib ∨ ia = finRotate (k + 2) ib := by
      simpa using (alternatingIndex_adj ia ib 0 1).mp hab
    exact ⟨hh, hx, hy⟩
  · rintro ⟨hij, hx, hy⟩
    refine ⟨alternatingIndex i 0, alternatingIndex j 1, ?_, ?_, ?_⟩
    · exact (alternatingIndex_adj i j 0 1).mpr (Or.inl ⟨rfl, rfl, hij⟩)
    · simp [alternatingCycleEmbedding_apply, alternatingVertex, hx]
    · simp [alternatingCycleEmbedding_apply, alternatingVertex, hy]

theorem alternatingTupleGraph_no_same {k : ℕ} {X Y : Type*}
    (p : Fin (k + 2) → X × Y × X) :
    (∀ a b : Fin (k + 2) × X,
      ¬ (alternatingTupleGraph p).Adj (Sum.inl a) (Sum.inl b)) ∧
    (∀ a b : Fin (k + 2) × Y,
      ¬ (alternatingTupleGraph p).Adj (Sum.inr a) (Sum.inr b)) := by
  constructor <;> intro a b hab <;>
    obtain ⟨u, v, huv, hu, hv⟩ := (SimpleGraph.map_adj _ _ _ _).mp hab
  all_goals
    obtain ⟨⟨i, c⟩, rfl⟩ := finProdFinEquiv.surjective u
    obtain ⟨⟨j, d⟩, rfl⟩ := finProdFinEquiv.surjective v
    change alternatingCycleEmbedding p (alternatingIndex i c) = _ at hu
    change alternatingCycleEmbedding p (alternatingIndex j d) = _ at hv
    rw [alternatingCycleEmbedding_apply] at hu hv
    fin_cases c <;> fin_cases d <;> simp [alternatingVertex] at hu hv
    have hh := (alternatingIndex_adj i j _ _).mp huv
    simpa using hh

theorem alternatingTupleGraph_le {k : ℕ} {X Y : Type*}
    (L : Fin (k + 2) → X → Y → Prop) (R : Fin (k + 2) → Y → X → Prop)
    (p : Fin (k + 2) → X × Y × X)
    (hL : ∀ i, L i (p i).1 (p i).2.1)
    (hR : ∀ i, R i (p i).2.1 (p i).2.2)
    (hc : ∀ i, (p i).2.2 = (p (finRotate (k + 2) i)).1) :
    alternatingTupleGraph p ≤ cyclicInterfaceGraph L R := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b => exact False.elim ((alternatingTupleGraph_no_same p).1 a b hab)
    | inr b =>
      obtain ⟨hij, hx, hy⟩ := (alternatingTupleGraph_adj_cross p a.1 b.1 a.2 b.2).mp hab
      change (a.1 = b.1 ∧ L a.1 a.2 b.2) ∨
        (a.1 = finRotate (k + 2) b.1 ∧ R b.1 b.2 a.2)
      rcases hij with hij | hij
      · left
        refine ⟨hij, ?_⟩
        rw [← hx, ← hy, ← hij]
        exact hL a.1
      · right
        refine ⟨hij, ?_⟩
        rw [← hx, ← hy, hij, ← hc b.1]
        exact hR b.1
  | inr a =>
    cases b with
    | inr b => exact False.elim ((alternatingTupleGraph_no_same p).2 a b hab)
    | inl b =>
      obtain ⟨hij, hx, hy⟩ := (alternatingTupleGraph_adj_cross p b.1 a.1 b.2 a.2).mp hab.symm
      change (b.1 = a.1 ∧ L b.1 b.2 a.2) ∨
        (b.1 = finRotate (k + 2) a.1 ∧ R a.1 a.2 b.2)
      rcases hij with hij | hij
      · left
        refine ⟨hij, ?_⟩
        rw [← hx, ← hy, ← hij]
        exact hL b.1
      · right
        refine ⟨hij, ?_⟩
        rw [← hx, ← hy, hij, ← hc a.1]
        exact hR a.1

end Oberwolfach
