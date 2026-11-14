module

public import Oberwolfach.FirstVortexMatchingHypotheses
public import Oberwolfach.FirstVortexNonempty

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach

theorem first_vortex_matching_hypotheses_of_positive_terminal_size
    {n d:ℕ} {U:Type} [Fintype U] {G:SimpleGraph (Fin n)}
    {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m) (he:0<ε)
    (hm:0<m) (hd:3≤d)
    (lam a γ ρ δ:ℝ) (hlam:0≤lam) (ha:a≤lam/(10*d)) (hγ:γ≤lam/(10*d))
    (hscale:∀(n A:ℕ),ε*n/2≤A→max a γ*n≤ρ*A ∧ 2*(max a γ*n)≤δ*A/4):
    2*max a (4*γ)≤lam/3 ∧
    max a γ*n≤ρ*(Q.extendedVertices 1).card ∧
    2*(max a γ*n)≤δ*(Q.extendedVertices 1).card/4:=
  first_vortex_matching_hypotheses Q he (Q.first_inner_vertex_nonempty he hm) hd lam a γ ρ δ hlam ha hγ hscale
end Oberwolfach
