module

public import Oberwolfach.FirstVortexOrderedSummedLossMatchingParameters
public import Oberwolfach.FirstVortexInnerSumSelectorRelativeActualVortex

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_ordered_summed_loss_relative_matching_parameters
    (r:ℕ) (α ε c rho eta localCap active θUpper assignUpper δold δlocal ρmatch globalRate factor:ℝ)
    (hα:0<α) (hε:0<ε) (hc:0<c) (hrho:0<rho) (heta:0<eta) (hlocal:0<localCap)
    (hactive:0<active) (hθUpper:0<θUpper) (hAssignUpper:0<assignUpper)
    (hδold:0<δold) (hgap:δold<δlocal) (hρmatch:0<ρmatch) (hGlobalRate:0<globalRate) (hfactor:0<factor):
    ∃t s lamAssign θ lam ξCap:ℝ,
      0<t ∧ t≤localCap ∧ 0<s ∧ 0<lamAssign ∧ lamAssign≤assignUpper ∧
      0<θ ∧ θ≤s ∧ θ≤factor*s ∧ θ≤θUpper ∧
      8*(θ*ε^2+lamAssign*ε)/((ρmatch/4)/40000)<active*ε/128 ∧
      0<lam ∧ 0<ξCap ∧ lam≤s ∧ lam≤globalRate ∧ ξCap≤s ∧ ξCap≤globalRate ∧
      lam≤θ ∧ lam≤α/128 ∧ lam≤δold*ε/32 ∧
      (∀ξ':ℝ,ξ'≤ξCap→lam+ξ'≤((ρmatch/4)/40000)*θ/4096 ∧
        ξ'/2≤(lamAssign-lam)*ε ∧ ξ'≤α/32 ∧
        ∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n)) (D mm:ℕ) (β:ℝ)
          (Q:Vortex U G D β ε mm),0<mm→ξ'*n≤(δlocal-δold)*((Q.extendedVertices 1).card:ℝ)) ∧
    ∃dMin:ℕ,∀d:ℕ,dMin≤d→3≤d ∧ (r+4)+2≤d ∧
      1/(d:ℝ)≤θ/1024 ∧ 1/(d:ℝ)≤(active*ε/128)/10 ∧
      (1/(((r+4:ℕ):ℝ)+1))/(d:ℝ)≤θ ∧
    ∃KMin N:ℕ,∀K:ℕ,KMin≤K→3≤K ∧
      5/((((r+4:ℕ):ℝ)+1)*(d:ℝ)+5)+(((r+4:ℕ):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2 ∧
      FirstVortexActualSummedLossNumerics r d K N ε c rho eta s θ :=by
  obtain ⟨lamAssign,θAssign,hAssign,hAssignUp,hθAssign,hθAssignUp,hCeiling⟩:=
    first_vortex_pre_spacing_assignment_choice ρmatch ε active assignUpper hρmatch hε hactive hAssignUpper
  let θcap:=min θAssign (min θUpper (1:ℝ))
  have hθcap:0<θcap:=by dsimp [θcap];positivity
  have hθcap1:θcap≤1:=(min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨t,s,θ,ht,hs,htcap,hθ,hθs,hθfactor,hθcap',dMin,hd⟩:=
    first_vortex_inner_sum_selector_relative_on_actual_vortex r ε c rho eta localCap θcap active factor
      hε hc hrho heta hlocal hθcap hθcap1 hactive hfactor
  have hθassign:θ≤θAssign:=hθcap'.trans (min_le_left _ _)
  have hθupper:θ≤θUpper:=hθcap'.trans ((min_le_right _ _).trans (min_le_left _ _))
  let upper:=min s globalRate
  have hupper:0<upper:=by dsimp [upper];positivity
  obtain ⟨lam,ξCap,hlam,hξ,hlamup,hξup,hlamθ,hlamα,hlamδ,hCap⟩:=
    first_vortex_matching_class_cap_with_upper α lamAssign ε δold δlocal θ ρmatch upper upper
      hα hAssign hε hδold hgap hθ hρmatch hupper hupper
  have hlams:lam≤s:=hlamup.trans (min_le_left _ _)
  have hlamglobal:lam≤globalRate:=hlamup.trans (min_le_right _ _)
  have hξs:ξCap≤s:=hξup.trans (min_le_left _ _)
  have hξglobal:ξCap≤globalRate:=hξup.trans (min_le_right _ _)
  refine ⟨t,s,lamAssign,θ,lam,ξCap,ht,htcap,hs,hAssign,hAssignUp,hθ,hθs,hθfactor,hθupper,
    hCeiling θ hθ.le hθassign,hlam,hξ,hlams,hlamglobal,hξs,hξglobal,hlamθ,hlamα,hlamδ,hCap,dMin,?_⟩
  intro d hdmin
  obtain ⟨hd3,hdr,hspace,hactiveSpace,hcut,KMin,N,hKN⟩:=hd d hdmin
  refine ⟨hd3,hdr,hspace,hactiveSpace,hcut,KMin,N,?_⟩
  intro K hK
  obtain ⟨hK3,hKcut,hNum⟩:=hKN K hK
  exact ⟨hK3,hKcut,hNum⟩
end Oberwolfach
