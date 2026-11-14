module

public import Oberwolfach.FirstVortexMatchingScale

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem vortex_first_inner_positive_from_terminal
    {n D m:ℕ} {U:Type} [Fintype U] {G:SimpleGraph (Fin n)} {β ε:ℝ}
    (Q:Vortex U G D β ε m) (he:0<ε) (hm:0<m):
    1≤(Q.extendedVertices 1).card:=by
  have hp:(0:ℝ)<ε*m/2:=by positivity
  have ht:(0:ℝ)<(Q.vertices Q.length).card:=lt_of_lt_of_le hp Q.terminal_lower
  have htNat:0<(Q.vertices Q.length).card:=by exact_mod_cast ht
  have hsub:Q.extendedVertices Q.length⊆Q.extendedVertices 1:=
    Q.extendedVertices_subset (by have h:=Q.length_pos;omega)
  have hcard:=Finset.card_le_card hsub
  rw [Q.extendedVertices_eq (le_refl Q.length)] at hcard
  omega

theorem first_vortex_host_scale_to_inner
    {n D m:ℕ} {U:Type} [Fintype U] {G:SimpleGraph (Fin n)} {β ε a γ ρ δ:ℝ}
    (Q:Vortex U G D β ε m) (he:0<ε) (hm:0<m)
    (hscale:∀(n A:ℕ),ε*n/2≤A→max a γ*n≤ρ*A ∧ 2*(max a γ*n)≤δ*A/4):
    max a γ*n≤ρ*(Q.extendedVertices 1).card ∧
    2*(max a γ*n)≤δ*(Q.extendedVertices 1).card/4:=by
  have hp:=vortex_first_inner_positive_from_terminal Q he hm
  have hsize:ε*(n:ℝ)/2≤(Q.extendedVertices 1).card:=by
    simpa only [Fintype.card_fin] using Q.first_inner_vertex_size_lower he hp
  exact hscale n _ hsize
end Oberwolfach
