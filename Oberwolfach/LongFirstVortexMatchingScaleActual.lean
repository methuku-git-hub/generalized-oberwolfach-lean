module

public import Oberwolfach.LongFirstVortexMatchingScaleChoice
public import Oberwolfach.FirstVortexMatchingScalePositive

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_first_vortex_matching_scale_actual
    (d:ℕ) (θ lam ε δold a γ:ℝ) (n:ℕ)
    (hd:0<d) (hθ:0<θ) (hlam:0<lam) (hε:0<ε)
    (hδ:0≤δold) (hδ1:δold≤1) (hlamδ:lam≤δold*ε/32)
    (hinv:1/(d:ℝ)≤θ/1024) (ha:a≤lam/(10*(d:ℝ))) (hγ:γ≤lam/(10*(d:ℝ)))
    (U:Type) [Fintype U] (G:SimpleGraph (Fin n)) (D m:ℕ) (β:ℝ)
    (Q:Vortex U G D β ε m) (hm:0<m):
    max a γ*(n:ℝ)≤(θ/4096)*(Q.extendedVertices 1).card := by
  have hinner:(ε/2)*(n:ℝ)≤((Q.extendedVertices 1).card:ℝ):=by
    have hh:=Q.first_inner_vertex_size_lower_of_positive_terminal_size hε hm
    simp only [Fintype.card_fin] at hh
    linarith
  exact (long_first_vortex_matching_scale_choice d θ lam ε δold a γ n _ hd hθ hlam hε hδ hδ1 hlamδ hinv ha hγ hinner).2.2
end Oberwolfach
