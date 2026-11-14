module

public import Oberwolfach.CanonicalCyclicTuples
public import Oberwolfach.CyclicFractionalGraphs

@[expose] public section

/-! Exact support of the canonical part-respecting cycle description. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem canonicalCycleGraph_le_iff {k : ℕ} {X Y : Type*}
    (L : Fin (k + 2) → X → Y → Prop) (R : Fin (k + 2) → Y → X → Prop)
    (v : Fin (k + 2) → X × Y) :
    alternatingTupleGraph (cyclicTupleOfVertices v) ≤ cyclicInterfaceGraph L R ↔
      ∀ i, L i (v i).1 (v i).2 ∧ R i (v i).2 (v (finRotate (k + 2) i)).1 := by
  constructor
  · intro h i
    have hleft := h ((alternatingTupleGraph_adj_cross (cyclicTupleOfVertices v)
      i i (v i).1 (v i).2).mpr ⟨Or.inl rfl, rfl, rfl⟩)
    have hright := h ((alternatingTupleGraph_adj_cross (cyclicTupleOfVertices v)
      (finRotate (k + 2) i) i (v (finRotate (k + 2) i)).1 (v i).2).mpr
        ⟨Or.inr rfl, rfl, rfl⟩)
    have hne := finRotate_ne_self i
    simpa only [cyclicInterfaceGraph, eq_self_iff_true, true_and, hne, hne.symm,
      false_and, or_false, false_or] using And.intro hleft hright
  · intro h
    exact alternatingTupleGraph_le L R (cyclicTupleOfVertices v)
      (fun i => (h i).1) (fun i => (h i).2) (fun _ => rfl)

theorem alternatingTupleGraph_canonicalize {k : ℕ} {X Y : Type*}
    (p : Fin (k + 2) → X × Y × X) :
    alternatingTupleGraph (cyclicTupleOfVertices (cyclicTupleVertices p)) =
      alternatingTupleGraph p := rfl

end Oberwolfach
