module

public import Oberwolfach.FirstVortexMatchingScale
public import Oberwolfach.FirstVortexMatchingJointMargins

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach

theorem first_vortex_matching_choice_at_level
    {n d K:ℕ} {U:Type} [Fintype U] {G:SimpleGraph (Fin n)}
    {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m) (he:0<ε)
    (hpos:1≤(Q.extendedVertices 1).card) (hd:0<d) (hK:0<K)
    (lam θ δ:ℝ) (hlam:0<lam) (hθ:0<θ) (hδ:0<δ):
    ∃ρ eps a γ:ℝ,0<ρ ∧ ρ≤θ/4096 ∧
      0<eps ∧ eps≤1 ∧ 3*eps≤lam*(θ/(100*(K:ℝ)^2)) ∧
      0<a ∧ a≤lam/(10*d) ∧ a≤θ/(200*(K:ℝ)^2) ∧
      0<γ ∧ γ≤eps ∧ γ≤eps/2 ∧ γ≤1/2 ∧ γ≤lam/(10*d) ∧ γ≤lam/10 ∧
      max a γ*n≤ρ*(Q.extendedVertices 1).card ∧
      2*(max a γ*n)≤δ*(Q.extendedVertices 1).card/4:=by
  obtain ⟨ρ,eps,a,γ,hρ,hρθ,heps,heps1,hepsrate,ha,haD,haθ,hγ,hγeps,hγeps2,hγhalf,hγD,hγlam,hscale⟩:=
    first_vortex_matching_joint_margins d K lam θ ε δ hd hK hlam hθ he hδ
  have hA:ε*(n:ℝ)/2≤(Q.extendedVertices 1).card:=by
    simpa only [Fintype.card_fin] using Q.first_inner_vertex_size_lower he hpos
  obtain ⟨hfirst,hsecond⟩:=hscale n (Q.extendedVertices 1).card hA
  exact ⟨ρ,eps,a,γ,hρ,hρθ,heps,heps1,hepsrate,ha,haD,haθ,hγ,hγeps,hγeps2,hγhalf,hγD,hγlam,hfirst,hsecond⟩
end Oberwolfach
