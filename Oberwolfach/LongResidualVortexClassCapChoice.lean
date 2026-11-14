module

public import Oberwolfach.LongResidualClassCapChoice
public import Oberwolfach.FirstVortexMatchingScalePositive

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_residual_vortex_class_cap_choice
    (α lam lamAssign ε δold δlocal:ℝ)
    (hα:0<α) (hε:0<ε) (hlam:lam<lamAssign) (hδ:δold<δlocal):
    ∃ξCap:ℝ,0<ξCap ∧ ∀ξPart:ℝ,0≤ξPart→ξPart≤ξCap→
      ξPart≤(2*α)/32 ∧ ξPart/2≤(lamAssign-lam)*ε ∧
      ∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n))
        (D m:ℕ) (β:ℝ) (Q:Vortex U G D β ε m),0<m→
        ξPart*n≤(δlocal-δold)*((Q.extendedVertices 1).card:ℝ) := by
  obtain ⟨ξCap,hCap,hCapProps⟩:=long_residual_class_cap_choice α lam lamAssign ε δold δlocal (ε/2)
    hα hε hlam hδ (by positivity)
  refine ⟨ξCap,hCap,?_⟩
  intro ξPart hξ hξcap
  obtain ⟨hdeg,hedges,hinner⟩:=hCapProps ξPart hξ hξcap
  refine ⟨hdeg,hedges,?_⟩
  intro n U _ G D m β Q hm
  have hsize:(ε/2)*(n:ℝ)≤((Q.extendedVertices 1).card:ℝ):=by
    have h:=Q.first_inner_vertex_size_lower_of_positive_terminal_size hε hm
    simp only [Fintype.card_fin] at h
    linarith
  exact hinner n ((Q.extendedVertices 1).card:ℝ) hsize
end Oberwolfach
