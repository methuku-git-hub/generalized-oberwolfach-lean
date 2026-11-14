module

public import Oberwolfach.PositiveOrdinaryCycleWeights

@[expose] public section
/-! The vertex load of an actual fractional ordinary-cycle decomposition. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_cycle_fractional_vertex_weight {V:Type} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) (r:ℕ) (w:OrdinaryCycle G r→ℝ)
    (hw:∀ e:G.edgeSet,∑ C,w C*ordinaryCycleIncidence G r C e=1):
    ∀ v,2*(∑ C,if v∈C.val.val.support then w C else 0)=(G.degree v:ℝ) := by
  intro v
  have hrow (u:V):
      (∑ C:OrdinaryCycle G r,if C.val.val.Adj v u then w C else 0)=
        if G.Adj v u then (1:ℝ) else 0:=by
    by_cases hG:G.Adj v u
    · let e:G.edgeSet:=⟨s(v,u),hG⟩
      have hh:=hw e
      rw [if_pos hG]
      convert hh using 1
      apply Finset.sum_congr rfl
      intro C _
      dsimp [ordinaryCycleIncidence,e]
      simp only [SimpleGraph.mem_edgeSet]
      split_ifs <;> simp_all
    · rw [if_neg hG]
      apply Finset.sum_eq_zero
      intro C _
      have hn:¬C.val.val.Adj v u:=fun h=>hG (C.property h)
      simp [hn]
  calc
    2*(∑ C:OrdinaryCycle G r,if v∈C.val.val.support then w C else 0) =
        ∑ C:OrdinaryCycle G r,∑ u:V,if C.val.val.Adj v u then w C else 0:=by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro C _
      have hdeg:(C.val.val.degree v:ℝ)=if v∈C.val.val.support then 2 else 0:=by
        by_cases hs:v∈C.val.val.support
        · have hh:=C.val.property.degree_zero_or_two v
          have hn:C.val.val.degree v≠0:=by
            intro hzero
            exact ((C.val.val.degree_eq_zero_iff_notMem_support v).mp hzero) hs
          have htwo:C.val.val.degree v=2:=hh.resolve_left hn
          simp [hs,htwo]
        · have hz: C.val.val.degree v=0:=
            (C.val.val.degree_eq_zero_iff_notMem_support v).mpr hs
          simp [hs,hz]
      have he:(∑ u:V,if C.val.val.Adj v u then w C else 0)=
          (∑ u:V,if C.val.val.Adj v u then (1:ℝ) else 0)*w C:=by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro u _
        split_ifs <;> simp
      rw [he,graph_adjacency_row_sum,hdeg]
      split_ifs <;> simp <;> ring
    _ = ∑ u:V,∑ C:OrdinaryCycle G r,if C.val.val.Adj v u then w C else 0:=by rw [Finset.sum_comm]
    _ = ∑ u:V,if G.Adj v u then (1:ℝ) else 0:=by simp_rw [hrow]
    _ = _:=graph_adjacency_row_sum G v
end Oberwolfach
