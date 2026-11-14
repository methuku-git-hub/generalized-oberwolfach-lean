module

public import Oberwolfach.CyclicGraphs
public import Oberwolfach.IntervalPathWeights

@[expose] public section

/-! A compatible cyclic tuple has a unique description by its chosen
vertices. This prevents multiplicity losses in pointwise weight bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def cyclicTupleOfVertices {k : ℕ} {X Y : Type*}
    (v : Fin (k + 2) → X × Y) (i : Fin (k + 2)) : X × Y × X :=
  ((v i).1, (v i).2, (v (finRotate (k + 2) i)).1)

def cyclicTupleVertices {k : ℕ} {X Y : Type*}
    (p : Fin (k + 2) → X × Y × X) (i : Fin (k + 2)) : X × Y :=
  ((p i).1, (p i).2.1)

theorem cyclicTupleVertices_inverse {k : ℕ} {X Y : Type*}
    (v : Fin (k + 2) → X × Y) :
    cyclicTupleVertices (cyclicTupleOfVertices v) = v := by
  funext i
  rfl

theorem cyclicTupleOfVertices_inverse {k : ℕ} {X Y : Type*}
    (p : Fin (k + 2) → X × Y × X)
    (hp : ∀ i, (p i).2.2 = (p (finRotate (k + 2) i)).1) :
    cyclicTupleOfVertices (cyclicTupleVertices p) = p := by
  funext i
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · exact (hp i).symm

theorem alternatingTupleGraph_determines_vertices {k : ℕ} {X Y : Type*}
    (p q : Fin (k + 2) → X × Y × X)
    (h : alternatingTupleGraph p = alternatingTupleGraph q) :
    cyclicTupleVertices p = cyclicTupleVertices q := by
  funext i
  have he : (alternatingTupleGraph p).Adj
      (Sum.inl (i, (p i).1)) (Sum.inr (i, (p i).2.1)) :=
    (alternatingTupleGraph_adj_cross p i i _ _).mpr ⟨Or.inl rfl, rfl, rfl⟩
  rw [h] at he
  obtain ⟨_, hx, hy⟩ := (alternatingTupleGraph_adj_cross q i i _ _).mp he
  exact Prod.ext hx.symm hy.symm

theorem canonicalCycleGraph_injective {k : ℕ} {X Y : Type*} :
    Function.Injective (fun v : Fin (k + 2) → X × Y =>
      alternatingTupleGraph (cyclicTupleOfVertices v)) := by
  intro v w h
  simpa only [cyclicTupleVertices_inverse] using
    alternatingTupleGraph_determines_vertices _ _ h

theorem compatible_cycle_tuple_injective {k : ℕ} {X Y : Type*}
    (p q : Fin (k + 2) → X × Y × X)
    (hp : ∀ i, (p i).2.2 = (p (finRotate (k + 2) i)).1)
    (hq : ∀ i, (q i).2.2 = (q (finRotate (k + 2) i)).1)
    (he : alternatingTupleGraph p = alternatingTupleGraph q) : p = q := by
  rw [← cyclicTupleOfVertices_inverse p hp, ← cyclicTupleOfVertices_inverse q hq]
  rw [alternatingTupleGraph_determines_vertices p q he]

theorem cyclic_weight_of_canonical_graph {k : ℕ} {X Y : Type*}
    [Fintype X] [Fintype Y]
    (ω : (Fin (k + 2) → X × Y × X) → ℝ)
    (hω : ∀ p, 0 ≤ ω p)
    (hc : ∀ p, 0 < ω p → ∀ i, (p i).2.2 = (p (finRotate (k + 2) i)).1)
    (v : Fin (k + 2) → X × Y) :
    (∑ p, if alternatingTupleGraph p = alternatingTupleGraph (cyclicTupleOfVertices v)
      then ω p else 0) = ω (cyclicTupleOfVertices v) := by
  classical
  have hp : ∀ i, (cyclicTupleOfVertices v i).2.2 =
      (cyclicTupleOfVertices v (finRotate (k + 2) i)).1 := fun _ => rfl
  rw [Finset.sum_eq_single (cyclicTupleOfVertices v)]
  · simp
  · intro p _ hne
    by_cases he : alternatingTupleGraph p = alternatingTupleGraph (cyclicTupleOfVertices v)
    · simp only [he, ite_true]
      by_contra hz
      have hpos := lt_of_le_of_ne (hω p) (Ne.symm hz)
      exact hne (compatible_cycle_tuple_injective p _ (hc p hpos) hp he)
    · simp only [he, ite_false]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

end Oberwolfach
