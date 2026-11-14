module

public import Oberwolfach.FirstVortexMatchingScale
public import Oberwolfach.FirstVortexRequiredDegreeAsymptotic
public import Oberwolfach.LongRequiredLocalDegreeCombinedMargin

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_required_degree_local_bound
    (ε δ θ lam:ℝ) (d:ℕ) (hε:0<ε) (hδ:0<δ)
    (hθ:θ≤δ/32) (hlam:lam≤δ*ε/32):
    ∃N:ℕ,∀n≥N,∀{U:Type} [Fintype U] {G Bad:SimpleGraph (Fin n)}
      {D m:ℕ} {β:ℝ} (Q:Vortex U G D β ε m),
      1≤(Q.extendedVertices 1).card→
      (∀v,(Bad.degree v:ℝ)≤2*θ*(Q.extendedVertices 1).card+(n:ℝ)^(3/4:ℝ)+lam*n+(6*d+2:ℕ))→
      ∀v,(Bad.degree v:ℝ)≤δ*(Q.extendedVertices 1).card/4:=by
  obtain ⟨N,hN⟩:=first_vortex_required_degree_errors_eventually ε δ d hε hδ
  refine ⟨N,?_⟩
  intro n hn U _ G Bad D m β Q hpos hdeg v
  have hA:ε*(n:ℝ)/2≤(Q.extendedVertices 1).card:=by
    simpa only [Fintype.card_fin] using Q.first_inner_vertex_size_lower hε hpos
  have he:=hN n hn (Q.extendedVertices 1).card hA
  have hlamN:lam*n≤δ*(Q.extendedVertices 1).card/16:=by
    have hn0:(0:ℝ)≤n:=Nat.cast_nonneg _
    have hh:=mul_le_mul_of_nonneg_right hlam hn0
    have ha:=mul_le_mul_of_nonneg_left hA hδ.le
    nlinarith only [hh,ha]
  exact (hdeg v).trans (long_required_local_degree_combined_numeric_margin n (Q.extendedVertices 1).card d θ lam ((n:ℝ)^(3/4:ℝ)) δ hδ.le hθ he hlamN)
end Oberwolfach
