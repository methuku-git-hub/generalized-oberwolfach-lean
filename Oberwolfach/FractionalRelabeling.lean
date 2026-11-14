module

public import Oberwolfach.FractionalDecompositions

@[expose] public section

/-! Relabelling preserves weights on actual subgraphs and all edge equations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem IsEmbeddedCycle.map {V W : Type*} {H : SimpleGraph V} {r : ℕ}
    (h : IsEmbeddedCycle H r) (f : V ↪ W) : IsEmbeddedCycle (H.map f) r := by
  obtain ⟨hr, e, rfl⟩ := h
  refine ⟨hr, e.trans f, ?_⟩
  rw [SimpleGraph.map_map]
  rfl

theorem HasFractionalDecomposition.map {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {P : SimpleGraph V → Prop}
    (h : HasFractionalDecomposition G P) (e : V ≃ W) :
    HasFractionalDecomposition (G.map e.toEmbedding)
      (fun K => ∃ H, P H ∧ K = H.map e.toEmbedding) := by
  obtain ⟨w, hw, hs, he⟩ := h
  apply fractionalDecomposition_of_indexed _ _ (fun H => H.map e.toEmbedding) w hw
  · intro H hH
    exact ⟨SimpleGraph.map_monotone _ (hs H hH).1, H, (hs H hH).2, rfl⟩
  · intro u v
    simp_rw [← SimpleGraph.comap_symm _ e]
    exact he (e.symm u) (e.symm v)

theorem HasFractionalDecomposition.mono_property {V : Type*}
    [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {P Q : SimpleGraph V → Prop} (h : HasFractionalDecomposition G P)
    (hPQ : ∀ H, P H → Q H) : HasFractionalDecomposition G Q := by
  obtain ⟨w, hw, hs, he⟩ := h
  exact ⟨w, hw, fun H hH => ⟨(hs H hH).1, hPQ H (hs H hH).2⟩, he⟩

theorem HasFractionalDecomposition.map_cycles {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {r : ℕ}
    (h : HasFractionalDecomposition G (fun H => IsEmbeddedCycle H r)) (e : V ≃ W) :
    HasFractionalDecomposition (G.map e.toEmbedding) (fun H => IsEmbeddedCycle H r) :=
  (h.map e).mono_property (by
    rintro K ⟨H, hH, rfl⟩
    exact hH.map e.toEmbedding)

end Oberwolfach
