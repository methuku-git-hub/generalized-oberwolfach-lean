module

public import Oberwolfach.FirstVortexNoMarkedCappedParameterChoices

@[expose] public section
/-! If the active tolerance is available before the vortex scale is chosen,
the matching and vortex scales can meet the active ceiling condition too. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_no_marked_active_parameter_choices
    (b ρ₀ θ δold δglobal lamList βfinal C₀ εcap active:ℝ)
    (hb:0<b) (hρ:0<ρ₀) (hθ:0<θ) (hδold:0<δold) (hδglobal:0<δglobal)
    (hcap:0<εcap) (hlist:0<lamList) (hβfinal:0≤βfinal) (hβbound:βfinal≤lamList/4)
    (hC:1≤C₀) (hactive:0<active):
    ∃αMatch εQ lam lamAssign:ℝ,
      0<αMatch ∧ (2*αMatch)/16≤b ∧
      (2*αMatch)/16≤((ρ₀/4)/40000)*θ/1024 ∧ 2*αMatch≤4*δglobal ∧
      0<εQ ∧ εQ≤εcap ∧ εQ≤δglobal ∧ βfinal+εQ≤lamList ∧
      εQ≤αMatch/(1000*C₀) ∧ εQ≤(ρ₀/4)/80000 ∧
      0<lam ∧ lam≤θ ∧ lam≤αMatch/128 ∧ lam≤δold*εQ/32 ∧ lam<lamAssign ∧
      8*(θ*εQ^2+lamAssign*εQ)/((ρ₀/4)/40000)<active*εQ/128 :=by
  let c:ℝ:=(ρ₀/4)/40000
  have hc:0<c:=by dsimp [c];positivity
  let bcap:ℝ:=active*c/(4096*(θ+δold+1))
  have hbcap:0<bcap:=by dsimp [bcap];positivity
  obtain ⟨αMatch,εQ,lam,lamOld,hα,hαb,hαθ,hαδ,hε,hεcap,hεδ,hlistBound,hεα,hερ,hlam,hlamθ,hlamα,hlamδ,hOld⟩:=
    first_vortex_no_marked_parameter_choices_capped b ρ₀ θ δold δglobal lamList βfinal C₀ (min εcap bcap)
      hb hρ hθ hδold hδglobal (lt_min hcap hbcap) hlist hβfinal hβbound hC
  have hεbc:εQ≤bcap:=hεcap.trans (min_le_right _ _)
  have hεorig:εQ≤εcap:=hεcap.trans (min_le_left _ _)
  have hmul:εQ*(θ+δold+1)≤active*c/4096:=by
    have h:=(le_div_iff₀ (show 0<4096*(θ+δold+1) by positivity)).mp hεbc
    nlinarith
  have hLam:2*lam≤δold*εQ/16:=by linarith
  have hrate:8*(θ*εQ^2+(2*lam)*εQ)/c<active*εQ/128:=by
    have hp:=mul_le_mul_of_nonneg_right hLam hε.le
    have hm:=mul_le_mul_of_nonneg_left hmul (show 0≤8*εQ/c by positivity)
    have heq:(8*εQ/c)*(active*c/4096)=active*εQ/512:=by field_simp;ring
    rw [heq] at hm
    have hbound:8*(θ*εQ^2+(2*lam)*εQ)/c≤active*εQ/512:=by
      apply (div_le_iff₀ hc).2
      have hcne:c≠0:=ne_of_gt hc
      have hm':8*εQ*(εQ*(θ+δold+1))≤active*εQ*c/512:=by
        have hmleft:(8*εQ/c)*(εQ*(θ+δold+1))=(8*εQ*(εQ*(θ+δold+1)))/c:=by ring
        rw [hmleft] at hm
        have hh:=(div_le_iff₀ hc).mp hm
        nlinarith
      nlinarith [sq_nonneg εQ]
    have hpos:0<active*εQ:=mul_pos hactive hε
    linarith
  exact ⟨αMatch,εQ,lam,2*lam,hα,hαb,hαθ,hαδ,hε,hεorig,hεδ,hlistBound,hεα,hερ,
    hlam,hlamθ,hlamα,hlamδ,by linarith,hrate⟩
end Oberwolfach
