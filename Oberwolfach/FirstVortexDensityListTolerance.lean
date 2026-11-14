module

public import Oberwolfach.FirstVortexMatchingJointMargins
public import Oberwolfach.FirstVortexMatchingScale
public import Oberwolfach.FirstVortexNonempty

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_event_density_and_matching_rates_with_global_and_list_tolerance
    (α ρ₀ C₀ θ δ εMax:ℝ) (d K:ℕ)
    (hα:0<α) (hεMax:0<εMax) (hρ₀:0<ρ₀) (hC:1≤C₀) (hθ:0<θ) (hδ:0<δ) (hd:0<d) (hK:0<K):
    ∃ε:ℝ,0<ε ∧ ε≤εMax ∧ ε≤δ ∧ ε≤1/100 ∧ ε≤α/(1000*C₀) ∧ ε≤(ρ₀/4)/80000 ∧
    ∀lam:ℝ,0<lam→
      ∃ρ eps a γ:ℝ,0<ρ ∧ ρ≤θ/4096 ∧
        0<eps ∧ eps≤1 ∧ 3*eps≤lam*(θ/(100*(K:ℝ)^2)) ∧
        0<a ∧ a≤lam/(10*d) ∧ a≤θ/(200*(K:ℝ)^2) ∧
        0<γ ∧ γ≤eps ∧ γ≤eps/2 ∧ γ≤1/2 ∧ γ≤lam/(10*d) ∧ γ≤lam/10 ∧
        ∀(V U:Type) [Fintype V] [Fintype U] (G:SimpleGraph V) (D m:ℕ) (β:ℝ)
          (Q:Vortex U G D β ε m),0<m→
          max a γ*(Fintype.card V:ℝ)≤ρ*(Q.extendedVertices 1).card ∧
          2*(max a γ*(Fintype.card V:ℝ))≤δ*(Q.extendedVertices 1).card/4 :=by
  let ε:ℝ:=min εMax (min δ (min (1/100) (min (α/(1000*C₀)) ((ρ₀/4)/80000))))
  have hC0:0<C₀:=by linarith
  have hε:0<ε:=by dsimp [ε];positivity
  have hεMax':ε≤εMax:=min_le_left _ _
  have hεrest:ε≤min δ (min (1/100) (min (α/(1000*C₀)) ((ρ₀/4)/80000))):=min_le_right _ _
  refine ⟨ε,hε,hεMax',hεrest.trans (min_le_left _ _),hεrest.trans ((min_le_right _ _).trans (min_le_left _ _)),
    hεrest.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))),
    hεrest.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))),?_⟩
  intro lam hlam
  obtain ⟨ρ,eps,a,γ,hρ,hρθ,heps,heps1,hepsrate,ha,haD,haθ,hγ,hγε,hγε2,hγhalf,hγD,hγlam,hscale⟩:=
    first_vortex_matching_joint_margins d K lam θ ε δ hd hK hlam hθ hε hδ
  refine ⟨ρ,eps,a,γ,hρ,hρθ,heps,heps1,hepsrate,ha,haD,haθ,hγ,hγε,hγε2,hγhalf,hγD,hγlam,?_⟩
  intro V U _ _ G D m β Q hm
  have hpos:=Q.first_inner_vertex_nonempty hε hm
  have hlower:=Q.first_inner_vertex_size_lower hε hpos
  exact hscale (Fintype.card V) (Q.extendedVertices 1).card hlower
end Oberwolfach
