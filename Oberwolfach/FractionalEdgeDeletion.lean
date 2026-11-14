module

public import Oberwolfach.SignedCycleEdgeIsolator
public import Oberwolfach.InducedFractionalCycles

@[expose] public section

/-! Fractional decompositions before and after deleting one specified edge,
and compatibility of that deletion with an injective vertex map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem graph_map_delete_edge {V W : Type*} (G : SimpleGraph V) (f : V ↪ W) (u v : V) :
    (G\SimpleGraph.edge u v).map f=G.map f\SimpleGraph.edge (f u) (f v) := by
  ext x y
  rw [SimpleGraph.map_adj,SimpleGraph.sdiff_adj]
  constructor
  · rintro ⟨a,b,hab,rfl,rfl⟩
    refine ⟨SimpleGraph.map_adj_apply.mpr hab.1,?_⟩
    simpa only [SimpleGraph.edge_adj,ne_eq,f.injective.eq_iff] using hab.2
  · rintro ⟨hab,hnot⟩
    rw [SimpleGraph.map_adj] at hab
    obtain ⟨a,b,hab,rfl,rfl⟩ := hab
    refine ⟨a,b,⟨hab,?_⟩,rfl,rfl⟩
    simpa only [SimpleGraph.edge_adj,ne_eq,f.injective.eq_iff] using hnot

theorem fractional_cycle_edge_deletion (r : ℕ) (hr : 3≤r) (α : ℝ) (hα : 0<α) :
    ∃ N : ℕ,∀ (V : Type) [Fintype V] [DecidableEq V],N≤Fintype.card V →
      ∀ G : SimpleGraph V,
      (∀ x,(cycleThreshold r+α)*Fintype.card V≤(G.degree x:ℝ)) →
      HasFractionalDecomposition G (fun C => IsEmbeddedCycle C r) ∧
      ∀ u v,G.Adj u v →
        HasFractionalDecomposition (G\SimpleGraph.edge u v) (fun C => IsEmbeddedCycle C r) := by
  obtain ⟨N₁,hN₁⟩ := cycle_fractional_positive_margin_finite r hr (α/2) (by positivity)
  obtain ⟨N₂,hN₂⟩ := eventually_constant_le_linear 1 (α/2) (by positivity)
  refine ⟨max N₁ N₂,?_⟩
  intro V _ _ hn G hdeg
  constructor
  · apply hN₁ V ((le_max_left _ _).trans hn) G
    intro x
    have ha : 0≤α*(Fintype.card V:ℝ) := mul_nonneg hα.le (Nat.cast_nonneg _)
    nlinarith [hdeg x]
  · intro u v huv
    apply hN₁ V ((le_max_left _ _).trans hn) (G\SimpleGraph.edge u v)
    intro x
    have hc := congrArg (fun a : ℕ => (a:ℝ)) (single_edge_deletion_degree G u v huv x)
    simp only [Nat.cast_add] at hc
    have hb : ((if x=u ∨ x=v then 1 else 0 : ℕ):ℝ)≤1 := by split_ifs <;> norm_num
    have hn' := hN₂ (Fintype.card V) ((le_max_right _ _).trans hn)
    have hg := hdeg x
    simp only [← SimpleGraph.ncard_neighborSet] at hc hg ⊢
    nlinarith

end Oberwolfach
