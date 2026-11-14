module

public import Oberwolfach.SuppliedVortexPrepareClassEveryProtection
public import Oberwolfach.SuppliedVortexClassCombinedCapacityGlobal
public import Oberwolfach.SuppliedVortexRegularBoundaryOrderedOutcome
public import Oberwolfach.SuppliedVortexRegularClassPreparedForEveryProtection
public import Oberwolfach.FirstVortexClassPrepareFromCommonTests
public import Oberwolfach.SuppliedVortexOutcomeBalancedDegreeMatchingGlobalBoundary
public import Oberwolfach.SuppliedVortexOutcomePreparedBalancedDegreeMatchingGlobalBoundary
public import Oberwolfach.FirstVortexPrepareOrientedCommonTests
public import Oberwolfach.SuppliedVortexOutcomePreparedOrientedMatching
public import Oberwolfach.SuppliedVortexOutcomePreparedProtectedMatching
public import Oberwolfach.FirstVortexPrepareProtectedCommonTests
public import Oberwolfach.SuppliedVortexOutcomePreparedFirstMatching

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance suppliedClassCommonToGlobalFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem supplied_vortex_regular_class_common_to_global
    (r k₀ K d:ℕ) (hr:2≤r) (hK:3≤K) (hm:7≤r+4) (hd:2≤d) (hd3:3≤d) (hdlarge:(r+4)+2≤d)
    (αRef sstar γRich tstar kstar θ ρ₀ eps lam ζret alpha γ:ℝ)
    (δold δlocal δglobal αMatch bmatch εQ ξ lamAssign ξPart:ℝ)
    (hθpos:0<θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hρ₀max:ρ₀≤1)
    (hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ)
    (hα:0<αMatch) (hlam:0<lam) (hε:0<εQ) (hδ:0<δold)
    (hgap:δold<δlocal) (hδglobal:0<δglobal) (hθglobal:10*θ≤δglobal)
    (hαsmall:(2*αMatch)/16≤((ρ₀/4)/40000)*θ/1024) (hαglobal:2*αMatch≤4*δglobal)
    (Nret:ℕ) (hNret:∀n:ℕ,Nret≤n→∀q errOrd:ℝ,
      q≤1/((((r+4):ℕ):ℝ)+1)→errOrd≤θ*n→
      (n:ℝ)*q/d+(((((r+4)+1)*d-1:ℕ):ℝ))*(2*((n:ℝ)^(3/4:ℝ)/d)+ζret*n)+errOrd≤4*θ*n)
    (hbmatch:0<bmatch) (hαb:(2*αMatch)/16≤bmatch)
    (hbd:bmatch≤((ρ₀/4)/40000)/16) (hεsmall:εQ≤(ρ₀/4)/80000)
    (hθδ:10*θ≤δold) (hθlocal:θ≤δold/32)
    (hlamlocal:lam≤δold*εQ/32) (hspacing:1/(d:ℝ)≤θ/1024)
    (heps:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hξ:4*ξ≤eps/2) (hξ0:0≤ξ)
    (C₀:ℝ) (hC:1≤C₀) (hehi:εQ≤αMatch/(1000*C₀)) (hlamhi:lam≤αMatch/128) (hlamθ:lam≤θ)
    (hγ:0≤γ) (ha0:0≤alpha) (hγε:γ≤eps) (heps1:eps≤1) (ha:alpha≤lam/(10*d)) (hγrate:γ≤lam/(10*d))
    (hζ:ζret≤θ/4096) (hζ0:0≤ζret) (ρscale:ℝ) (hρscale:ρscale≤θ/4096) (hρscale0:0≤ρscale)
    (hξdeg:ξPart≤(2*αMatch)/32) (hξedges:ξPart/2≤(lamAssign-lam)*εQ)
    (hcutHost:5/(((((r+4):ℕ):ℝ)+1)*(d:ℝ)+5)+((((r+4):ℕ):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2):
    ∃N:ℕ,∀n:ℕ,N≤n→∀(U:Type) [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hclass:∀u,factorPreparationClass (F u) K=none)
    (P Zpart:SimpleGraph (Fin n)) (Dpart Bpart:ℕ) (mpart:Fin 2→ℕ) (π:Equiv.Perm (Fin n))
    (Dnat vsize:ℕ) (βQ:ℝ) (Q:Vortex U P Dnat βQ εQ vsize)
    (hreg:P.IsRegularOfDegree Dnat) (hDv:0<Dnat) (hρhi:initialIndexDensity U Dnat≤1)
    (hρlo:ρ₀ ≤ initialIndexDensity U Dnat) (hDlo:(n:ℝ)/2≤Dnat) (hDhi:(Dnat:ℝ)≤2*n) (hvsize:0<vsize)
    (hsize:initialIndexDensity U Dnat*(Dnat:ℝ)=2*Fintype.card U)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (hscale:max alpha γ*n≤ρscale*(Q.extendedVertices 1).card)
    (hmargin:ξPart*n≤(δlocal-δold)*(Q.extendedVertices 1).card)
    (β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel:ℝ)
    (BM:ℝ) (BO:Fin K→ℝ) (t₀ Δ τ:ℝ) (hτ:0≤τ)
    (size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr:ℕ)
    (weight:(Fin ((r+4)+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (τWeight Asrc:ℝ) (hBM:0<BM)
    (hw:SuccessorSequenceWeightConditions P π (3*d) Dnat τWeight Asrc BM weight)
    (hBO:∀i,0<BO i) (hw0:∀i C,0≤w i C)
    (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i)),
    ∀(hn:1≤n) (hDvR:0<(Dnat:ℝ)),
    SuppliedVortexFixedSpacingRegularBoundaryOrderedOutcome r k₀ K d hr hK hm hd αRef sstar γRich tstar kstar θ ρ₀ (initialIndexDensity U Dnat) Dnat eps lam ζret alpha γ
      hθpos hθ hρ₀ hρlo hρhi hDvR hcut β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel
      BM BO t₀ ξ Δ τ size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr n hn U F hF Allowed hAllowed hsize hclass P Zpart Dpart Bpart mpart ξPart π weight w Dnat vsize βQ εQ Q hpres →
    SuppliedVortexRegularClassGlobalForEveryProtection r k₀ K d hr hK hm hd αRef sstar γRich tstar kstar θ ρ₀ (initialIndexDensity U Dnat) Dnat eps lam ζret alpha γ
      hθpos hθ hρ₀ hρlo hρhi hDvR hcut β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel
      BM BO t₀ ξ Δ τ size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr n hn U F hF Allowed hAllowed hsize hclass P Zpart Dpart Bpart mpart ξPart π weight w Dnat vsize βQ εQ Q hpres δlocal δglobal αMatch bmatch lamAssign :=by
  have hδlocal:0<δlocal:=lt_trans hδ hgap
  have hθlocal':θ≤δlocal/32:=by linarith
  have hlamlocal':lam≤δlocal*εQ/32:=by nlinarith
  obtain ⟨Np,hp⟩:=supplied_vortex_prepare_regular_class_for_every_protection r k₀ K d hr hK hm hd hd3 αRef sstar γRich tstar kstar θ ρ₀ eps lam ζret alpha γ δold δlocal αMatch bmatch εQ ξ lamAssign ξPart hθpos hθ hρ₀ hcut hα hlam hε hδ hbmatch hαb hbd hεsmall hθδ hθlocal hlamlocal hspacing heps hξ hξ0 C₀ hC hehi hlamhi hlamθ hγ ha0 hγε heps1 ha hγrate hζ hζ0 ρscale hρscale hξdeg hξedges hcutHost
  obtain ⟨Ng,hg⟩:=supplied_vortex_class_every_protection_global_from_prepared r k₀ K d hr hK hm hd hd3 hdlarge αRef sstar γRich tstar kstar θ ρ₀ eps lam ζret alpha γ δlocal δglobal αMatch bmatch εQ ξ lamAssign ξPart hθpos hθ hρ₀ hρ₀max hcut hα hlam hε hδlocal hδglobal hbmatch hαb hαsmall hαglobal Nret hNret hbd hεsmall hθglobal hθlocal' hlamlocal' hspacing heps hξ hξ0 C₀ hC hehi hlamhi hlamθ hγ hγε heps1 ha hγrate hζ hζ0 ρscale hρscale hρscale0 hcutHost
  refine ⟨max Np Ng,?_⟩
  intro n hnN U _ _ F hF Allowed hAllowed hclass P Zpart Dpart Bpart mpart π Dnat vsize βQ Q hreg hDv hρhi hρlo hDlo hDhi hvsize hsize hpres hnoshort hscale hmargin β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel BM BO t₀ Δ τ hτ size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr weight w τWeight Asrc hBM hw hBO hw0 hwupper hn hDvR hout
  have hp':=hp n (by omega) U F hF Allowed hAllowed hclass P Zpart Dpart Bpart mpart π Dnat vsize βQ Q hreg hDv hρhi hρlo hDlo hDhi hvsize hsize hpres hnoshort hscale hmargin β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel BM BO t₀ Δ τ hτ size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr weight w τWeight Asrc hBM hw hBO hw0 hwupper hn hDvR
  have hg':=hg n (by omega) U F hF Allowed hAllowed hclass P Zpart Dpart Bpart mpart π Dnat vsize βQ Q hreg hDv hρhi hρlo hDlo hDhi hvsize hsize hpres hnoshort hscale β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel BM BO t₀ Δ τ hτ size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr weight w τWeight Asrc hBM hw hBO hw0 hwupper hn hDvR
  have hdecP:suppliedClassEveryProtectionPrepareFin n=suppliedClassCommonToGlobalFin n:=Subsingleton.elim _ _
  have hdecPK:suppliedClassEveryProtectionPrepareFin K=suppliedClassCommonToGlobalFin K:=Subsingleton.elim _ _
  have hdecG:suppliedClassCombinedGlobalFin n=suppliedClassCommonToGlobalFin n:=Subsingleton.elim _ _
  have hdecGK:suppliedClassCombinedGlobalFin K=suppliedClassCommonToGlobalFin K:=Subsingleton.elim _ _
  try rw [hdecP] at hp'
  try rw [hdecPK] at hp'
  try rw [hdecG] at hg'
  try rw [hdecGK] at hg'
  exact hg' (hp' hout)
end Oberwolfach
