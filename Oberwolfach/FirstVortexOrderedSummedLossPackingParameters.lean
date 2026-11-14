module

public import Oberwolfach.FirstVortexOrderedSummedLossRelativeRetentionParameters
public import Oberwolfach.FirstVortexRelativeSpacingPackingChoice

@[expose] public section
/-! Choose the packing tolerance in the same hierarchy as the actual
vortex, matching, class-edit, retained-spoke and common-balance rates. -/
set_option autoImplicit false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_ordered_summed_loss_packing_parameters
    (r:ℕ) (α ε c rho eta localCap active θUpper assignUpper δold δlocal ρmatch globalRate βfinal κPackCap:ℝ)
    (hα:0<α) (hε:0<ε) (hε1:ε≤1/4) (hc:0<c) (hrho:0<rho) (heta:0<eta) (hlocal:0<localCap)
    (hactive:0<active) (hθUpper:0<θUpper) (hAssignUpper:0<assignUpper)
    (hδold:0<δold) (hgap:δold<δlocal) (hρmatch:0<ρmatch) (hGlobalRate:0<globalRate) (hβ:0<βfinal) (hκcap:0<κPackCap):
    ∃t s lamAssign θ lam ξCap κPack:ℝ,
      0<t ∧ t≤localCap ∧ 0<s ∧ 0<lamAssign ∧ lamAssign≤assignUpper ∧
      0<θ ∧ θ≤s ∧ θ≤θUpper ∧
      0<κPack ∧ κPack≤s/2 ∧ κPack≤κPackCap/2 ∧ 10*θ≤κPack*(βfinal/4) ∧
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
    ∃ζret ζlocal ηBalance κaux:ℝ,
      FirstVortexRetentionBalanceRates r d ε active θ s c ζret ζlocal ηBalance κaux ∧
    ∃KMin N:ℕ,∀K:ℕ,KMin≤K→3≤K ∧
      5/((((r+4:ℕ):ℝ)+1)*(d:ℝ)+5)+(((r+4:ℕ):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2 ∧
      FirstVortexActualSummedLossNumerics r d K N ε c rho eta s θ :=by
  let upper:=min θUpper ((βfinal/80)*κPackCap)
  have hupper:0<upper:=by dsimp [upper];positivity
  have hfactor:0<βfinal/80:=by positivity
  obtain ⟨t,s,lamAssign,θ,lam,ξCap,ht,htcap,hs,hAssign,hAssignUp,hθ,hθs,hθfactor,hθupper,
    hCeiling,hlam,hξ,hlams,hlamglobal,hξs,hξglobal,hlamθ,hlamα,hlamδ,hCap,dMin,hd⟩:=
    first_vortex_ordered_summed_loss_relative_retention_parameters r α ε c rho eta localCap active upper assignUpper δold δlocal ρmatch globalRate (βfinal/80)
      hα hε hε1 hc hrho heta hlocal hactive hupper hAssignUpper hδold hgap hρmatch hGlobalRate hfactor
  have hθUpper:θ≤θUpper:=hθupper.trans (min_le_left _ _)
  have hθcap:θ≤(βfinal/80)*κPackCap:=hθupper.trans (min_le_right _ _)
  obtain ⟨κPack,hκ,hκs,hκcap',hκlower⟩:=
    first_vortex_relative_spacing_packing_choice βfinal s κPackCap θ hβ hs hκcap hθ hθfactor hθcap
  exact ⟨t,s,lamAssign,θ,lam,ξCap,κPack,ht,htcap,hs,hAssign,hAssignUp,hθ,hθs,hθUpper,
    hκ,hκs,hκcap',hκlower,hCeiling,hlam,hξ,hlams,hlamglobal,hξs,hξglobal,hlamθ,hlamα,hlamδ,hCap,dMin,hd⟩
end Oberwolfach
