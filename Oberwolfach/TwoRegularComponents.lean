module

public import Oberwolfach.Definitions
public import Mathlib.Combinatorics.SimpleGraph.Matching

@[expose] public section

/-! The component-order condition in the main target is exactly the cycle-length
condition for finite 2-regular graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem regular_two_isCycles {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : G.IsRegularOfDegree 2) : G.IsCycles := by
  intro v _
  rw [SimpleGraph.ncard_neighborSet, hG v]

theorem cycle_support_eq_tail_support {V : Type*} {G : SimpleGraph V}
    {v : V} {p : G.Walk v v} (hp : p.IsCycle) (x : V) :
    x ∈ p.support ↔ x ∈ p.tail.support := by
  rw [← SimpleGraph.Walk.cons_support_tail hp.not_nil, List.mem_cons]
  constructor
  · rintro (rfl | hx)
    · exact p.tail.end_mem_support
    · exact hx
  · exact Or.inr

theorem cycle_length_eq_support_ncard {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {v : V} {p : G.Walk v v} (hp : p.IsCycle) :
    p.length = ({x | x ∈ p.support} : Set V).ncard := by
  have heq : ({x | x ∈ p.support} : Set V) = (p.tail.support.toFinset : Set V) := by
    ext x
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, List.mem_toFinset]
    exact cycle_support_eq_tail_support hp x
  rw [heq, Set.ncard_coe_finset, List.toFinset_card_of_nodup hp.isPath_tail.support_nodup,
    SimpleGraph.Walk.length_support]
  exact (SimpleGraph.Walk.length_tail_add_one hp.not_nil).symm

theorem regular_two_component_cycle {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsRegularOfDegree 2) (v : V) :
    ∃ p : G.Walk v v, p.IsCycle ∧
      (∀ x, x ∈ p.support ↔ G.Reachable v x) ∧
      p.length = Nat.card {x : V // G.Reachable v x} ∧
      (∀ x y, G.Reachable v x → (p.toSubgraph.Adj x y ↔ G.Adj x y)) := by
  have hcycles := regular_two_isCycles G hG
  have hn : (G.neighborSet v).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [SimpleGraph.ncard_neighborSet, hG v]
    decide
  obtain ⟨p, hp, hverts⟩ := hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := G.connectedComponentMk v) (by rfl) hn
  have hs (x : V) : x ∈ p.support ↔ G.Reachable v x := by
    rw [← SimpleGraph.Walk.mem_verts_toSubgraph, hverts,
      SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq]
    exact G.reachable_comm
  refine ⟨p, hp, hs, ?_, ?_⟩
  · rw [cycle_length_eq_support_ncard hp]
    have heq : ({x | x ∈ p.support} : Set V) = {x | G.Reachable v x} :=
      Set.ext hs
    rw [heq]
    rfl
  · intro x y hx
    apply hp.adj_toSubgraph_iff_of_isCycles hcycles
    exact p.mem_verts_toSubgraph.mpr ((hs x).mpr hx)

theorem AllowedCycleLengths_iff_component_cycles {n : ℕ}
    (F : SimpleGraph (Fin n)) (hF : F.IsRegularOfDegree 2) (S : Set ℕ) :
    AllowedCycleLengths F S ↔
      ∀ v, ∃ p : F.Walk v v, p.IsCycle ∧ p.length ∈ S ∧
        (∀ x, x ∈ p.support ↔ F.Reachable v x) := by
  constructor
  · intro h v
    obtain ⟨p, hp, hs, hlen, _⟩ := regular_two_component_cycle F hF v
    exact ⟨p, hp, hlen ▸ h v, hs⟩
  · intro h v
    obtain ⟨p, hp, hlen, hs⟩ := h v
    have hc : p.length = Nat.card {x : Fin n // F.Reachable v x} := by
      rw [cycle_length_eq_support_ncard hp]
      have heq : ({x | x ∈ p.support} : Set (Fin n)) = {x | F.Reachable v x} :=
        Set.ext hs
      rw [heq]
      rfl
    exact hc ▸ hlen

end Oberwolfach
