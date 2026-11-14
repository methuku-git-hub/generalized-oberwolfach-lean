module

public import Oberwolfach.FirstVortexGlobalThenLocalParameterHierarchy
public import Oberwolfach.FirstVortexActualCallerNumericResult
public import Oberwolfach.FirstVortexSummedLossLocalCapMono

@[expose] public section
/-! The ordered matching and retention choices discharge the caller's
numerical hypotheses for every subsequently selected seed and class rate. -/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

/-- Enlarging the local cap preserves all actual-vortex loss numerics. -/
theorem first_vortex_actual_summed_loss_numerics_local_cap_mono
    (r d K N:ℕ) (ε c cLocal rho eta s θ:ℝ) (hcLocal:c≤cLocal)
    (h:FirstVortexActualSummedLossNumerics r d K N ε c rho eta s θ):
    FirstVortexActualSummedLossNumerics r d K N ε cLocal rho eta s θ := by
  intro n hn U inst G D m β Q hm I u hu lam' eps' Δ' ξ' κ' ζ' η' hlam heps hΔ hξ hκ hζ hη hlamS hrate hΔ8 hξS hκS hζS hηS
  have hw := h n hn U G D m β Q hm u hu lam' eps' Δ' ξ' κ' ζ' η'
    hlam heps hΔ hξ hκ hζ hη hlamS hrate hΔ8 hξS hκS hζS hηS
  exact first_vortex_summed_loss_local_cap_mono n d _ c cLocal rho eta θ _ _ ξ' κ' Δ' ζ' η' _
    (by positivity) hcLocal hw

theorem first_vortex_packing_parameters_supply_caller_budgets
    (r:ℕ) (ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax tGlobal:ℝ)
    (α ε c cLocal localCap active θUpper assignUpper δold δlocal lamCap κPackCap:ℝ)
    (hρ₀:0<ρ₀) (hβ:0<βfinal) (hε:0<ε) (hεInner:ε≤εInner) (hactive:0<active)
    (hcLocal:c≤cLocal) (hcGlobal:c≤min cap (1:ℝ))
    (hθMax:θUpper≤θmax) (hθGlobal:10*θUpper≤δglobal) (hθOne:θUpper≤1)
    (hκRoot:κPackCap/2≤Real.sqrt δglobal/4) (hκGlobal:κPackCap/2≤min cap (1:ℝ)/1024)
    (hlamCap:lamCap≤min tGlobal (3*min ζmax Δmax))
    (hData:FirstVortexAmbientGlobalData r ρ₀ cap (βfinal/2) rho eta ζmax Δmax δLoss εInner δglobal θmax tGlobal)
    (hPack:FirstVortexOrderedPackingData r α ε c rho eta localCap active θUpper assignUpper δold δlocal ρ₀ lamCap βfinal κPackCap):
    ∃t s lamAssign θ lam ξCap κPack:ℝ,
      0<t ∧ t≤localCap ∧ 0<s ∧ 0<lamAssign ∧ lamAssign≤assignUpper ∧
      0<θ ∧ θ≤s ∧ θ≤θUpper ∧
      0<κPack ∧ κPack≤s/2 ∧ κPack≤κPackCap/2 ∧ 10*θ≤κPack*(βfinal/4) ∧
      8*(θ*ε^2+lamAssign*ε)/((ρ₀/4)/40000)<active*ε/128 ∧
      0<lam ∧ 0<ξCap ∧ lam≤s ∧ lam≤lamCap ∧ ξCap≤s ∧ ξCap≤lamCap ∧
      lam≤θ ∧ lam≤α/128 ∧ lam≤δold*ε/32 ∧
      (∀ξ':ℝ,ξ'≤ξCap→lam+ξ'≤((ρ₀/4)/40000)*θ/4096 ∧
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
      FirstVortexActualSummedLossNumerics r d K N ε c rho eta s θ ∧
      ∀eps Δ ξPart:ℝ,0<eps→0≤Δ→Δ≤eps/8→0≤ξPart→ξPart≤ξCap→
        3*eps≤lam*(θ/(100*(K:ℝ)^2))→
      ∃ hδ:0<δglobal, ∃ hθ:0<θ, ∃ hθδ:10*θ≤δglobal, ∃ hspacing:1/(d:ℝ)≤θ/1024,
        FirstVortexActualCallerNumericResult r d K ρ₀ cap rho eta δLoss εInner δglobal
          ε cLocal active θ lamAssign lam eps Δ ξPart ζret ηBalance κPack βfinal hδ hθ hθδ hspacing :=by
  obtain ⟨t,s,lamAssign,θ,lam,ξCap,κPack,ht,htcap,hs,hAssign,hAssignUp,hθ,hθs,hθUpper,
    hκ,hκs,hκcap,hκlower,hCeiling,hlam,hξ,hlams,hlamglobal,hξs,hξglobal,hlamθ,hlamα,hlamδ,hCap,dMin,hd⟩:=hPack
  have hδ:0<δglobal:=by obtain ⟨_,_,_,_,_,_,hδ,_,_,_,_,_,_,_,_,_,_,_,_,_,_⟩:=hData;exact hδ
  have hθmax:θ≤θmax:=hθUpper.trans hθMax
  have hθone:θ≤1:=hθUpper.trans hθOne
  have hθδ:10*θ≤δglobal:=by linarith
  have hκs':κPack≤s:=by linarith
  have hκroot':κPack≤Real.sqrt δglobal/4:=hκcap.trans hκRoot
  have hκglobal':κPack≤min cap (1:ℝ)/1024:=hκcap.trans hκGlobal
  have hlamcap':lam≤min tGlobal (3*min ζmax Δmax):=hlamglobal.trans hlamCap
  have hξglobal':ξCap≤tGlobal:=hξglobal.trans (hlamCap.trans (min_le_left _ _))
  refine ⟨t,s,lamAssign,θ,lam,ξCap,κPack,ht,htcap,hs,hAssign,hAssignUp,hθ,hθs,hθUpper,
    hκ,hκs,hκcap,hκlower,hCeiling,hlam,hξ,hlams,hlamglobal,hξs,hξglobal,hlamθ,hlamα,hlamδ,hCap,dMin,?_⟩
  intro d hdmin
  obtain ⟨hd3,hdr,hspace,hactiveSpace,hcut,ζret,ζlocal,ηBalance,κaux,hRet,KMin,N,hKN⟩:=hd d hdmin
  have hRetCopy:=hRet
  obtain ⟨hζ,hζlocal,hbal,hκaux,hζs,hζc,hζθ,hζlocalCap,hζscale,hbals,hbalc,hκauxs,hκauxret,hκauxbal,hretTail⟩:=hRet
  have hcScale:c/1024≤min cap (1:ℝ)/1024:=div_le_div_of_nonneg_right hcGlobal (by norm_num)
  have hζglobal:ζret≤min cap (1:ℝ)/1024:=hζc.trans hcScale
  have hbalglobal:ηBalance≤min cap (1:ℝ)/1024:=hbalc.trans hcScale
  refine ⟨hd3,hdr,hspace,hactiveSpace,hcut,ζret,ζlocal,ηBalance,κaux,hRetCopy,KMin,N,?_⟩
  intro K hK
  obtain ⟨hK3,hKcut,hNum⟩:=hKN K hK
  refine ⟨hK3,hKcut,hNum,?_⟩
  intro eps Δ ξPart heps hΔ0 hΔ hξ0 hξPart hepsRate
  have hNumLocal:=first_vortex_actual_summed_loss_numerics_local_cap_mono r d K N ε c cLocal rho eta s θ hcLocal hNum
  have hξPartS:ξPart≤s:=hξPart.trans hξs
  have hξPartGlobal:ξPart≤tGlobal:=hξPart.trans hξglobal'
  refine ⟨hδ,hθ,hθδ,hspace,?_⟩
  exact first_vortex_actual_caller_numeric_bundle r d K N ρ₀ cap (βfinal/2) rho eta ζmax Δmax δLoss εInner δglobal θmax tGlobal
    ε cLocal s active θ lamAssign lam eps Δ ξPart ζret ηBalance κPack βfinal hβ rfl hδ hθδ hκlower hData hNumLocal
    (by omega) (by omega) hρ₀ hε hεInner hactive hs hθ hθone hθmax hlam hlamθ heps hlams hlamcap' hepsRate hΔ0 hΔ
    hξ0 hξPartS hξPartGlobal hκ.le hκs' hκroot' hκglobal' hζ.le hζs hζglobal hbal.le hbals hbalglobal hspace hactiveSpace hCeiling
end Oberwolfach
