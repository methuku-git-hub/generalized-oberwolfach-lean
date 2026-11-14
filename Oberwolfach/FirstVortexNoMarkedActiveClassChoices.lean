module

public import Oberwolfach.FirstVortexNoMarkedActiveChoices
public import Oberwolfach.FirstVortexMatchingClassCapChoice

@[expose] public section
/-! Choose the early active ceiling and the later class-edit cap with the
same vortex and assignment parameters. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_no_marked_active_class_choices
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
      ∀ξ':ℝ,ξ'≤ξCap→lam+ξ'≤((ρ₀/4)/40000)*θ/4096 ∧
        ξ'/2≤(lamAssign-lam)*εQ ∧ ξ'≤αMatch/32 ∧
        ∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n)) (D mm:ℕ) (β:ℝ)
          (Q:Vortex U G D β εQ mm),0<mm→ξ'*n≤(δlocal-δold)*((Q.extendedVertices 1).card:ℝ) :=by
  obtain ⟨α,ε,lam0,lamAssign,hα,hαb,hαθ,hαδ,hε,hεcap,hεδ,hlistBound,hεα,hερ,
    hlam0,hlam0θ,hlam0α,hlam0δ,hassign,hRate⟩:=
    first_vortex_no_marked_active_parameter_choices b ρ₀ θ δold δglobal lamList βfinal C₀ εcap active
      hb hρ hθ hδold hδglobal hcap hlist hβfinal hβbound hC hactive
  have hAssignPos:0<lamAssign:=lt_trans hlam0 hassign
  obtain ⟨lam,ξCap,hlam,hξ,hlamθ,hlamα,hlamδ,hCap⟩:=
    first_vortex_matching_class_cap_choice α lamAssign ε δold δlocal θ ρ₀
      hα hAssignPos hε hδold hgap hθ hρ
  have hgapLam:lam<lamAssign:=by
    have hh:=(hCap ξCap le_rfl).2.1
    nlinarith
  exact ⟨α,ε,lam,lamAssign,ξCap,hα,hαb,hαθ,hαδ,hε,hεcap,hεδ,hlistBound,hεα,hερ,
    hlam,hAssignPos,hξ,hlamθ,hlamα,hlamδ,hgapLam,hRate,hCap⟩
end Oberwolfach
