module

public import Oberwolfach.SaturatedVertexBound

@[expose] public section
/-! A component uses each target at most once, so avoiding the labels that
were saturated before the component preserves the vertex-load bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V:Type} [Fintype V] [DecidableEq V]

theorem prescribed_component_load_update (f:V→ℕ) (t:ℝ) (T:Finset V)
    (hbound:∀ v,(f v:ℝ)≤t+1)
    (havoid:Disjoint T (Finset.univ.filter (fun v=>(t:ℝ)≤f v))):
    ∀ v,((f v + if v∈T then 1 else 0:ℕ):ℝ)≤t+1 := by
  intro v
  by_cases hv:v∈T
  · have hnot:¬ t≤(f v:ℝ):=by
      intro hh
      exact (Finset.disjoint_left.mp havoid) hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v,hh⟩)
    have hlt:(f v:ℝ)<t:=lt_of_not_ge hnot
    simp only [if_pos hv,Nat.cast_add,Nat.cast_one]
    linarith
  · simpa [hv] using hbound v
end Oberwolfach
