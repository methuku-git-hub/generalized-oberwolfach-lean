module

public import Oberwolfach.FirstVortexLocalLoadPowerMargins

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_local_load_margins
    (ε δ θ:ℝ) (d:ℕ) (hε:0<ε) (hδ:0<δ) (hθ:0<θ)
    (hθδ:10*θ≤δ) (hspacing:1/(d:ℝ)≤θ/1024):
    ∃N:ℕ,∀n:ℕ,N≤n→∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n))
      (D m:ℕ) (β:ℝ) (Q:Vortex U G D β ε m),
      G.IsRegularOfDegree D→0<D→initialIndexDensity U D≤1→0<m→
      let A:ℝ:=(Q.extendedVertices 1).card
      let H:ℝ:=(Q.extendedIndices 1).card
      H≤A ∧ 4/(d:ℝ)≤δ/8 ∧ 4*A^(3/4:ℝ)≤δ*A/8 ∧ A^(3/4:ℝ)≤(θ/4096)*A :=by
  obtain ⟨N,hN⟩:=first_vortex_local_load_power_margins ε δ θ hε hδ hθ
  refine ⟨max N 1,?_⟩
  intro n hn U _ G D m β Q hreg hD hρ hm A H
  have hnN:N≤n:=le_trans (le_max_left _ _) hn
  have hn0:0<n:=by omega
  have hp:=hN n hnN U G D m β Q hm
  exact ⟨first_vortex_inner_hub_card_le_vertex_card Q hreg hn0 hD hε.le hρ,
    first_vortex_spacing_load_margin θ δ d hθ.le hθδ hspacing,hp.1,hp.2⟩
end Oberwolfach
