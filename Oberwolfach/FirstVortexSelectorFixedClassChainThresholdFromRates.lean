module

public import Oberwolfach.FirstVortexSelectorChainThresholdFromRates
public import Oberwolfach.FirstVortexSameSampleFixedClassChainNamedThreshold

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_selector_fixed_class_chain_threshold_from_rates
    (r d K e:ℕ) (ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate:ℝ)
    (βList εLevel εAbs εRob γRich kstar tstar hostCap bmatch α ε:ℝ)
    (δold δlocal θUpper θ lam lamAssign ξCap eps Δ ξ ξPart ζret ζlocal ηBalance κaux s c cSmall cLocal active κPack:ℝ)
    (hInitial:FirstVortexInitialMatchingVortexRates ρ₀ δglobal βList βfinal εLevel εInner εAbs εRob γRich kstar tstar hostCap bmatch α ε)
    (hGlobal:FirstVortexGlobalRatesContinuation r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate)
    (hRet:FirstVortexRetentionBalanceRates r d ε active θ s c ζret ζlocal ηBalance κaux)
    (hρ₀:0<ρ₀) (hρ₀hi:ρ₀≤1) (hδold:0<δold) (hδold1:δold≤1)
    (hθUpper:θ≤θUpper) (hθold:θUpper≤δold/32) (hθone:θUpper≤1/100)
    (hlam:0<lam) (hlamθ:lam≤θ) (hlamδ:lam≤δold*ε/32)
    (hCap:∀ξ':ℝ,ξ'≤ξCap→lam+ξ'≤((ρ₀/4)/40000)*θ/4096 ∧
      ξ'/2≤(lamAssign-lam)*ε ∧ ξ'≤α/32 ∧
      ∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n)) (D mm:ℕ) (β:ℝ)
        (Q:Vortex U G D β ε mm),0<mm→ξ'*n≤(δlocal-δold)*((Q.extendedVertices 1).card:ℝ))
    (hd:3≤d) (hdlarge:(r+4)+2≤d) (hK:3≤K) (hm:7≤r+4)
    (heps:0<eps) (hepsRate:3*eps≤lam*(θ/(100*(K:ℝ)^2)))
    (hΔeps:Δ≤eps/8) (hξ:4*ξ≤eps/2) (hξ0:0≤ξ) (hξPart:ξPart≤ξCap)
    (hβ:0<βfinal) (hβone:βfinal≤1) (hκ:0<κPack) (hc:cSmall≤cLocal)
    (hNum:∃hδ:0<δglobal,∃hθ:0<θ,∃hθδ:10*θ≤δglobal,∃hspacing:1/(d:ℝ)≤θ/1024,
      FirstVortexActualCallerNumericResult r d K ρ₀ cap rho eta δLoss εInner δglobal
        ε cSmall active θ lamAssign lam eps Δ ξPart ζret ηBalance κPack βfinal hδ hθ hθδ hspacing):
    ∃N:ℕ,FirstVortexSameSampleFixedClassChainAt α lam lamAssign ε δold δlocal δglobal θ eps ξ ρ₀ bmatch ξPart ζret d K r Δ rho δLoss εInner eta e
      cap cLocal active ηBalance κPack βfinal N :=by
  obtain ⟨hbmatch,hbd,hα,hαb,_,hε,_,_,_,_,_,_,_,_,_,hεsmall,hprecise,_⟩:=hInitial
  obtain ⟨hrho,heta,_,_,_,_,_,_,_,hetaR,_⟩:=hGlobal.1
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,Nret,hNret,_⟩:=hRet
  obtain ⟨hδglobal,hθ,hθglobal,hspacing,hNum⟩:=hNum
  have hθlocal:θ≤δold/32:=hθUpper.trans hθold
  have hθδ:10*θ≤δold:=by linarith
  have hθhi:θ≤1/100:=hθUpper.trans hθone
  exact first_vortex_same_sample_fixed_class_chain_named_threshold α lam lamAssign ε δold δlocal δglobal θ eps ξ ρ₀ bmatch ξPart ζret d K r Δ rho δLoss εInner eta e
    cap cSmall cLocal active ηBalance κPack βfinal hα hlam hε hδold hδold1 hθ heps hρ₀ hbmatch hαb hbd hεsmall hθδ hθlocal hθhi hlamδ hspacing
    hd hK hm hepsRate hξ hξ0 hρ₀hi hδglobal hθglobal hprecise ξCap hξPart hCap hlamθ hdlarge Nret hNret hrho heta hetaR hβ hβone hκ hc hNum
end Oberwolfach
