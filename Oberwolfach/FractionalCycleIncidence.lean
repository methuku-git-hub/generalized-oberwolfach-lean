module

public import Oberwolfach.FractionalDecompositions
public import Oberwolfach.GraphDeletion

@[expose] public section

/-! Edge and vertex loads for weights supported on actual embedded cycles. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem graph_adjacency_row_sum {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (v : V) :
    (∑ u, if H.Adj v u then (1:ℝ) else 0) = H.degree v := by
  have he : Finset.univ.filter (H.Adj v) = H.neighborFinset v := by
    ext u
    simp
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, he,
    SimpleGraph.card_neighborFinset_eq_degree]

theorem IsEmbeddedCycle.degree_zero_or_two {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {r : ℕ} (h : IsEmbeddedCycle H r) (v : V) :
    H.degree v=0 ∨ H.degree v=2 := by
  obtain ⟨hr,f,rfl⟩ := h
  have hh := mapped_regular_degree_or_zero (SimpleGraph.cycleGraph r) (d:=2)
    (by intro i; simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using cycleGraph_regular hr i) f v
  simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hh

theorem IsEmbeddedCycle.exists_adj {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {r : ℕ} (h : IsEmbeddedCycle H r) : ∃ u v,H.Adj u v := by
  obtain ⟨hr,f,rfl⟩ := h
  let i : Fin r := ⟨0,by omega⟩
  have hd : ((SimpleGraph.cycleGraph r).map f).degree (f i)=2 := by
    have hh := SimpleGraph.degree_map_apply (SimpleGraph.cycleGraph r) f i
    simpa only [← SimpleGraph.ncard_neighborSet] using hh.trans (cycleGraph_regular hr i)
  have hp : 0<(((SimpleGraph.cycleGraph r).map f).neighborFinset (f i)).card := by
    simpa only [SimpleGraph.card_neighborFinset_eq_degree,hd] using (by decide : 0<2)
  obtain ⟨v,hv⟩ := Finset.card_pos.mp hp
  exact ⟨f i,v,(SimpleGraph.mem_neighborFinset _ _ _).mp hv⟩

theorem fractional_cycle_coefficient_le_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : ℕ) (w : SimpleGraph V → ℝ)
    (hw : ∀ H,0≤w H) (hs : ∀ H,0<w H → H≤G ∧ IsEmbeddedCycle H r)
    (he : ∀ u v,(∑ H,if H.Adj u v then w H else 0)=if G.Adj u v then 1 else 0)
    (C : SimpleGraph V) : w C≤1 := by
  by_cases hp : 0<w C
  · obtain ⟨u,v,hC⟩ := (hs C hp).2.exists_adj
    have hb := Finset.single_le_sum (s:=Finset.univ)
      (f:=fun H : SimpleGraph V => if H.Adj u v then w H else 0)
      (fun H _ => by split_ifs;exact hw H;exact le_refl _) (Finset.mem_univ C)
    simpa only [if_pos hC,he,if_pos ((hs C hp).1 hC)] using hb
  · linarith [hw C]

theorem signed_cycle_vertex_load {V : Type*} [Fintype V] [DecidableEq V]
    (r : ℕ) (w : SimpleGraph V → ℝ)
    (hs : ∀ H,w H≠0 → IsEmbeddedCycle H r) (v : V) :
    2*(∑ H,if H.degree v≠0 then w H else 0)=
      ∑ u,∑ H,if H.Adj v u then w H else 0 := by
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro H _
  have he : (∑ u,if H.Adj v u then w H else 0)=(H.degree v:ℝ)*w H := by
    calc
      _ = (∑ u,if H.Adj v u then (1:ℝ) else 0)*w H := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro u _
        split_ifs <;> simp
      _ = _ := by rw [graph_adjacency_row_sum]
  rw [he]
  by_cases hw : w H=0
  · simp [hw]
  · rcases (hs H hw).degree_zero_or_two v with h0|h2
    · simp [h0]
    · simp [h2]

end Oberwolfach
