module

public import Oberwolfach.FirstVortexClassOrderedEditMargins
public import Oberwolfach.FirstClassRetargetLoadMargin

@[expose] public section
/-! A cap chosen before the selector makes its class-edit tolerance satisfy
both the degree and first-vortex load margins. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_class_edit_cap_for_selector
    (α ε δold δlocal ξupper:ℝ) (hα:0<α) (hε:0<ε)
    (hgap:δold<δlocal) (hupper:0<ξupper):
    ∃ξcap:ℝ,0<ξcap ∧ ξcap≤ξupper ∧
    ∀ξ:ℝ,ξ≤ξcap→ξ≤α/32 ∧
      ∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n))
        (D m:ℕ) (β:ℝ) (Q:Vortex U G D β ε m),0<m→
        ξ*n≤(δlocal-δold)*((Q.extendedVertices 1).card:ℝ) :=by
  let ξcap:=min ξupper (min (α/32) ((δlocal-δold)*ε/2))
  have hgap':0<δlocal-δold:=sub_pos.mpr hgap
  have hcap:0<ξcap:=by dsimp [ξcap]; positivity
  refine ⟨ξcap,hcap,min_le_left _ _,?_⟩
  intro ξ hξ
  have hαcap:ξcap≤α/32:=(min_le_right _ _).trans (min_le_left _ _)
  have hloadcap:ξcap≤(δlocal-δold)*ε/2:=(min_le_right _ _).trans (min_le_right _ _)
  refine ⟨hξ.trans hαcap,?_⟩
  intro n U _ G D m β Q hm
  have hsize:ε*(n:ℝ)/2≤((Q.extendedVertices 1).card:ℝ):=by
    simpa only [Fintype.card_fin] using Q.first_inner_vertex_size_lower_of_positive_terminal_size hε hm
  have hh:=mul_le_mul_of_nonneg_right (hξ.trans hloadcap) (show (0:ℝ)≤n by positivity)
  have hh':(δlocal-δold)*(ε*(n:ℝ)/2)≤(δlocal-δold)*((Q.extendedVertices 1).card:ℝ):=
    mul_le_mul_of_nonneg_left hsize hgap'.le
  nlinarith only [hh,hh']
end Oberwolfach
