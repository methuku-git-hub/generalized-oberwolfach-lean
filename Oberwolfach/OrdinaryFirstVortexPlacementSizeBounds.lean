module

public import Oberwolfach.MarkedInitialInnerHubBound
public import Oberwolfach.MarkedInitialInnerVertexBound

@[expose] public section
/-! A vortex chosen with a sufficiently small contraction supplies all three
first-level size inputs for the tracked placement. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_first_vortex_placement_size_bounds
    {n q D m:ℕ} (P:SimpleGraph (Fin n)) (β ε εearly αcap δ:ℝ)
    (Q:Vortex (Fin q) P D β ε m)
    (hε:0≤ε) (hcard:q≤n) (hearly:ε≤εearly) (hcap:ε≤αcap) (hδ:ε≤δ/2):
    ((Q.extendedVertices 1).card:ℝ)≤εearly*n ∧
    ((Q.extendedIndices 1).card:ℝ)≤αcap*n ∧
    ((Q.extendedIndices 1).card:ℝ)≤δ*n/2 :=by
  have hV:=marked_initial_inner_vertex_bound Q hε
  have hU:=marked_initial_inner_hub_bound P D m β ε Q hε (by simpa using hcard)
  simp only [Fintype.card_fin] at hV hU
  have hn:(0:ℝ)≤n:=by positivity
  refine ⟨?_,?_,?_⟩
  · exact hV.trans (mul_le_mul_of_nonneg_right hearly hn)
  · exact hU.trans (mul_le_mul_of_nonneg_right hcap hn)
  · have hh:=mul_le_mul_of_nonneg_right hδ hn
    linarith
end Oberwolfach
