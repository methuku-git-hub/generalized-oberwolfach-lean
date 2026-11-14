module

public import Oberwolfach.FirstVortexMatchingScalePositive
public import Oberwolfach.VortexSizeBounds

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem Vortex.first_inner_indices_nonempty
    {V U:Type} [Fintype V] [Fintype U] {G:SimpleGraph V} {D m:ℕ} {β ε ρ₀:ℝ}
    (Q:Vortex U G D β ε m) (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hD:(Fintype.card V:ℝ)/2≤D) (hρ₀:0<ρ₀) (hρ:ρ₀ ≤ initialIndexDensity U D)
    (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hm:0<m):
    (Q.extendedIndices 1).Nonempty := by
  have hlen:1≤Q.length:=Q.length_pos
  have hv:(Q.extendedVertices 1).Nonempty:=Finset.card_pos.mp (Q.first_inner_vertex_nonempty hε hm)
  have hvpos:0<((Q.vertices 1).card:ℝ):=by
    rw [Q.extendedVertices_eq hlen] at hv
    exact_mod_cast hv.card_pos
  have hI:=Q.index_size_lower hreg hn hD hρ₀ hρ hβ hβ1 hlen
  have hIpos:0<((Q.indices 1).card:ℝ):=lt_of_lt_of_le (by positivity) hI
  have hcard:0<(Q.indices 1).card:=by exact_mod_cast hIpos
  rw [Q.extendedIndices_eq hlen]
  exact Finset.card_pos.mp hcard
end Oberwolfach
