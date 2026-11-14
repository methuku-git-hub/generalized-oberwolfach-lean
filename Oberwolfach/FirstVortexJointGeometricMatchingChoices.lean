module

public import Oberwolfach.FirstVortexGeometricActiveRateChoice

@[expose] public section
/-! The matching scale and the structural active-spoke scale can be chosen
together when the active tolerance is fixed before the vortex scale. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_joint_geometric_matching_choices
    (b ρ₀ θ δold δlocal δglobal lamList βfinal C₀ εcap active:ℝ)
    (hb:0<b) (hρ:0<ρ₀) (hθ:0<θ) (hδold:0<δold) (hgap:δold<δlocal)
    (hδglobal:0<δglobal) (hcap:0<εcap) (hlist:0<lamList)
    (hβfinal:0≤βfinal) (hβbound:βfinal≤lamList/4) (hC:1≤C₀) (hactive:0<active):
    ∃αMatch εQ lam lamAssign ξCap:ℝ,
      0<αMatch ∧ (2*αMatch)/16≤b ∧
      (2*αMatch)/16≤((ρ₀/4)/40000)*θ/1024 ∧ 2*αMatch≤4*δglobal ∧
      0<εQ ∧ εQ≤εcap ∧ εQ≤δglobal ∧ βfinal+εQ≤lamList ∧
      εQ≤αMatch/(1000*C₀) ∧ εQ≤(ρ₀/4)/80000 ∧
      0<lam ∧ 0<lamAssign ∧ 0<ξCap ∧ lam≤θ ∧ lam≤αMatch/128 ∧
      lam≤δold*εQ/32 ∧ lam<lamAssign ∧
      8*(θ*εQ^2+lamAssign*εQ)/((ρ₀/4)/40000)<active*εQ/128 ∧
      8*((1/2:ℝ)*εQ^2)/((ρ₀/4)/40000)<active*εQ/128 ∧
      ∀ξ':ℝ,ξ'≤ξCap→lam+ξ'≤((ρ₀/4)/40000)*θ/4096 ∧
        ξ'/2≤(lamAssign-lam)*εQ ∧ ξ'≤αMatch/32 ∧
        ∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n)) (D mm:ℕ) (β:ℝ)
          (Q:Vortex U G D β εQ mm),0<mm→ξ'*n≤(δlocal-δold)*((Q.extendedVertices 1).card:ℝ) :=by
  let ecap:=active*((ρ₀/4)/40000)/1024
  have hecap:0<ecap:=by dsimp [ecap];positivity
  obtain ⟨α,ε,lam,lamAssign,ξCap,hα,hαb,hαθ,hαδ,hε,hεcap,hεδ,hlistBound,hεα,hερ,
    hlam,hAssign,hξ,hlamθ,hlamα,hlamδ,hgapLam,hRate,hCap⟩:=
    first_vortex_no_marked_active_class_choices b ρ₀ θ δold δlocal δglobal lamList βfinal C₀ (min εcap ecap) active
      hb hρ hθ hδold hgap hδglobal (lt_min hcap hecap) hlist hβfinal hβbound hC hactive
  have hsmall:ε≤active*((ρ₀/4)/40000)/1024:=hεcap.trans (min_le_right _ _)
  have hgeom:=first_vortex_geometric_active_rate_of_scale ρ₀ ε active hρ hε hactive hsmall
  exact ⟨α,ε,lam,lamAssign,ξCap,hα,hαb,hαθ,hαδ,hε,hεcap.trans (min_le_left _ _),hεδ,hlistBound,hεα,hερ,
    hlam,hAssign,hξ,hlamθ,hlamα,hlamδ,hgapLam,hRate,hgeom,hCap⟩
end Oberwolfach
