module

public import Oberwolfach.VortexLocalRowSizeConditions

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach

theorem Vortex.first_inner_vertex_nonempty
    {V U:Type} [Fintype V] [Fintype U] {G:SimpleGraph V}
    {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m) (he:0<ε) (hm:0<m):
    1≤(Q.extendedVertices 1).card:=by
  have hmul:(0:ℝ)<ε*m/2:=by positivity
  have hterm:(0:ℝ)<(Q.vertices Q.length).card:=lt_of_lt_of_le hmul Q.terminal_lower
  have htermN:0<(Q.vertices Q.length).card:=by exact_mod_cast hterm
  have hL:1≤Q.length:=Q.length_pos
  have hsub:=Q.extendedVertices_subset hL
  rw [Q.extendedVertices_eq (le_refl Q.length)] at hsub
  have hcard:=Finset.card_le_card hsub
  omega
end Oberwolfach
