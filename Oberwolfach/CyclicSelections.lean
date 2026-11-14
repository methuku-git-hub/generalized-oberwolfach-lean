module

public import Oberwolfach.CanonicalCycleSupport

@[expose] public section

/-! Part-respecting cycles as selections of one vertex in each tagged class. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

def taggedClass {I X : Type*} : (I × X) ⊕ (I × X) → I ⊕ I
  | Sum.inl a => Sum.inl a.1
  | Sum.inr a => Sum.inr a.1

def taggedValue {I X : Type*} : (I × X) ⊕ (I × X) → X
  | Sum.inl a => a.2
  | Sum.inr a => a.2

theorem taggedEncoding_injective {I X : Type*} :
    Function.Injective (fun v : (I × X) ⊕ (I × X) => (taggedClass v, taggedValue v)) := by
  intro u v h
  cases u with
  | inl a =>
    cases v with
    | inl b => simpa only [taggedClass, taggedValue, Prod.mk.injEq, Sum.inl.injEq, Prod.ext_iff] using h
    | inr b => simp [taggedClass] at h
  | inr a =>
    cases v with
    | inl b => simp [taggedClass] at h
    | inr b => simpa only [taggedClass, taggedValue, Prod.mk.injEq, Sum.inr.injEq, Prod.ext_iff] using h

def cyclicSelectionGraph {k : ℕ} {X : Type*}
    (f : Fin (k + 2) ⊕ Fin (k + 2) → X) :
    SimpleGraph ((Fin (k + 2) × X) ⊕ (Fin (k + 2) × X)) :=
  alternatingTupleGraph (cyclicTupleOfVertices (fun i => (f (Sum.inl i), f (Sum.inr i))))

theorem cyclicSelectionGraph_injective {k : ℕ} {X : Type*} :
    Function.Injective (cyclicSelectionGraph (k := k) (X := X)) := by
  intro f g h
  have he := canonicalCycleGraph_injective h
  funext i
  cases i with
  | inl i => exact congrArg Prod.fst (congrFun he i)
  | inr i => exact congrArg Prod.snd (congrFun he i)

def cyclicSelectionOfTuple {k : ℕ} {X : Type*}
    (p : Fin (k + 2) → X × X × X) : Fin (k + 2) ⊕ Fin (k + 2) → X :=
  Sum.elim (fun i => (p i).1) (fun i => (p i).2.1)

theorem cyclicSelectionGraph_ofTuple {k : ℕ} {X : Type*}
    (p : Fin (k + 2) → X × X × X) :
    cyclicSelectionGraph (cyclicSelectionOfTuple p) = alternatingTupleGraph p := rfl

theorem cyclicSelection_adj_forces {k : ℕ} {X : Type*}
    (f : Fin (k + 2) ⊕ Fin (k + 2) → X)
    (u v : (Fin (k + 2) × X) ⊕ (Fin (k + 2) × X))
    (h : (cyclicSelectionGraph f).Adj u v) :
    f (taggedClass u) = taggedValue u ∧ f (taggedClass v) = taggedValue v := by
  cases u with
  | inl a =>
    cases v with
    | inl b => exact False.elim ((alternatingTupleGraph_no_same _).1 a b h)
    | inr b =>
      have hh := (alternatingTupleGraph_adj_cross _ a.1 b.1 a.2 b.2).mp h
      exact hh.2
  | inr a =>
    cases v with
    | inr b => exact False.elim ((alternatingTupleGraph_no_same _).2 a b h)
    | inl b =>
      have hh := (alternatingTupleGraph_adj_cross _ b.1 a.1 b.2 a.2).mp h.symm
      exact ⟨hh.2.2, hh.2.1⟩

end Oberwolfach
