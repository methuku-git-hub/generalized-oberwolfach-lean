module

public import Oberwolfach.SuppliedVortexClassCommonToBalanced
public import Oberwolfach.SuppliedVortexClassBalancedFullyUniform
public import Oberwolfach.SuppliedVortexClassChosenCorrectionProof
public import Oberwolfach.SuppliedVortexClassBalancedDegreesEveryProtectionProof
public import Oberwolfach.SuppliedVortexClassCommonToGlobal
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
local instance suppliedClassCommonSpacingChosenFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem supplied_vortex_regular_class_common_to_chosen_uniform_spacing
    (r k₀ K:ℕ) (hr:2≤r) (hK:3≤K) (hm:7≤r+4)
    (αRef sstar γRich tstar kstar θ ρ₀ eps lam ζret alpha γ:ℝ)
    (δold δlocal δglobal αMatch bmatch εQ ξ lamAssign δcorr fprot:ℝ) (hαRef:0<αRef) (hδcorr:0<δcorr) (hfprot:0≤fprot)
    (hθpos:0<θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hρ₀max:ρ₀≤1)
    (hα:0<αMatch) (hlam:0<lam) (hε:0<εQ) (hδ:0<δold)
    (hgap:δold<δlocal) (hδglobal:0<δglobal) (hθglobal:10*θ≤δglobal)
    (hαsmall:(2*αMatch)/16≤((ρ₀/4)/40000)*θ/1024) (hαglobal:2*αMatch≤4*δglobal)
    (hbmatch:0<bmatch) (hαb:(2*αMatch)/16≤bmatch)
    (hbd:bmatch≤((ρ₀/4)/40000)/16) (hεsmall:εQ≤(ρ₀/4)/80000)
    (hθδ:10*θ≤δold) (hθlocal:θ≤δold/32)
    (hlamlocal:lam≤δold*εQ/32)
    (heps:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hξ:4*ξ≤eps/2) (hξ0:0≤ξ)
    (C₀:ℝ) (hC:1≤C₀) (hehi:εQ≤αMatch/(1000*C₀)) (hlamhi:lam≤αMatch/128) (hlamθ:lam≤θ)
    (hγ:0≤γ) (ha0:0≤alpha) (hγε:γ≤eps) (heps1:eps≤1)
    (hζ:ζret≤θ/4096) (hζ0:0≤ζret) (ρscale:ℝ) (hρscale:ρscale≤θ/4096) (hρscale0:0≤ρscale)
:
    ∃c:ℝ,0<c ∧ ∀ξPart:ℝ,0<ξPart→
    ξPart≤min (min (c/4) (δcorr/16)) (αRef*(ρ₀/200)^2/4)→
    ξPart≤(2*αMatch)/32→ξPart/2≤(lamAssign-lam)*εQ→ξPart+δcorr≤ξ→
    ∀(d:ℕ) (hd:2≤d) (hd3:3≤d) (hdlarge:(r+4)+2≤d)
    (hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ)
    (Nret:ℕ) (hNret:∀n:ℕ,Nret≤n→∀q errOrd:ℝ,
      q≤1/((((r+4):ℕ):ℝ)+1)→errOrd≤θ*n→
      (n:ℝ)*q/d+(((((r+4)+1)*d-1:ℕ):ℝ))*(2*((n:ℝ)^(3/4:ℝ)/d)+ζret*n)+errOrd≤4*θ*n)
    (hspacing:1/(d:ℝ)≤θ/1024) (ha:alpha≤lam/(10*d)) (hγrate:γ≤lam/(10*d))
    (hcutHost:5/(((((r+4):ℕ):ℝ)+1)*(d:ℝ)+5)+((((r+4):ℕ):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2),
    ∃N:ℕ,∀n:ℕ,N≤n→∀(U:Type) [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hclass:∀u,factorPreparationClass (F u) K=none)
    (P Zpart:SimpleGraph (Fin n)) (Dpart Bpart:ℕ) (mpart:Fin 2→ℕ) (hmpart:mpart 0=Fintype.card U) (π:Equiv.Perm (Fin n))
    (Dnat vsize:ℕ) (βQ:ℝ) (Q:Vortex U P Dnat βQ εQ vsize)
    (hreg:P.IsRegularOfDegree Dnat) (hDv:0<Dnat) (hρhi:initialIndexDensity U Dnat≤1)
    (hρlo:ρ₀ ≤ initialIndexDensity U Dnat) (hDlo:(n:ℝ)/2≤Dnat) (hDhi:(Dnat:ℝ)≤2*n) (hvsize:0<vsize)
    (hsize:initialIndexDensity U Dnat*(Dnat:ℝ)=2*Fintype.card U)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (hscale:max alpha γ*n≤ρscale*(Q.extendedVertices 1).card)
    (hmargin:ξPart*n≤(δlocal-δold)*(Q.extendedVertices 1).card)
    (β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel:ℝ)
    (BM:ℝ) (BO:Fin K→ℝ) (t₀ Δ τ:ℝ) (hτ:0≤τ) (hΔcorr:ξPart+δcorr≤Δ)
    (hfbound:fprot≤(αRef*(ρ₀/200)^2/16)*n)
    (hdegree:∀v,(P.degree v:ℝ)=(Dnat:ℝ))
    (hmin:∀v,(1/2+αRef)*(n:ℝ)≤P.degree v)
    (size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr:ℕ)
    (weight:(Fin ((r+4)+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (τWeight Asrc:ℝ) (hBM:0<BM)
    (hw:SuccessorSequenceWeightConditions P π (3*d) Dnat τWeight Asrc BM weight)
    (hBO:∀i,0<BO i) (hw0:∀i C,0≤w i C)
    (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i)),
    ∀(hn:1≤n) (hDvR:0<(Dnat:ℝ))
    (βlist lamList ζList βfinal η γList pstar:ℝ)
    (hn2:2≤n) (hu:Fintype.card U≤n) (hεδ:εQ≤δglobal)
    (hβfinal:0<βfinal) (hβfinal1:βfinal≤1) (hδbound:δglobal≤(βfinal/100)^2)
    (hnβ:100/βfinal≤(n:ℝ)) (hnδ:2/Real.sqrt δglobal≤(n:ℝ))
    (hγList:0≤γList) (hpstar:0≤pstar) (hp:pstar≤(initialIndexDensity U Dnat)*(1/100)/2)
    (hβlist:0≤βlist) (hlamList:0≤lamList) (hζList:0≤ζList) (hΔζ:Δ≤ζList)
    (hP:∀x,(1/2+γList)*n≤(P.degree x:ℝ))
    (herror:(n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γList*pstar^2*n)
    (hlistMargin:βlist*n+(n:ℝ)^(3/4:ℝ)≤γList*pstar^2*n*(1/100:ℝ))
    (hlistBudget:(lamList+2*ζList)*n≤βlist*n)
    (hsub:(n:ℝ)^(3/4:ℝ)≤η*n)
    (htrim:βfinal+εQ+1/(100*((r+4:ℕ):ℝ))+η≤lamList),
    SuppliedVortexFixedSpacingRegularBoundaryOrderedOutcome r k₀ K d hr hK hm hd αRef sstar γRich tstar kstar θ ρ₀ (initialIndexDensity U Dnat) Dnat eps lam ζret alpha γ
      hθpos hθ hρ₀ hρlo hρhi hDvR hcut β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel
      BM BO t₀ ξ Δ τ size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr n hn U F hF Allowed hAllowed hsize hclass P Zpart Dpart Bpart mpart ξPart π weight w Dnat vsize βQ εQ Q hpres →
    SuppliedVortexClassAtChosenCorrection r k₀ K d hr hK hm hd αRef sstar γRich tstar kstar θ ρ₀ (initialIndexDensity U Dnat) Dnat eps lam ζret alpha γ
      hθpos hθ hρ₀ hρlo hρhi hDvR hcut β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel
      BM BO t₀ ξ Δ τ size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr n hn U F hF Allowed hAllowed hsize hclass P Zpart Dpart Bpart mpart ξPart π weight w Dnat vsize βQ εQ Q hpres δlocal δglobal αMatch bmatch lamAssign δcorr fprot :=by
  obtain ⟨c,hc,hCorr⟩:=supplied_vortex_prepare_class_balanced_correction_fully_uniform αRef ρ₀ δcorr hαRef hρ₀ hδcorr
  refine ⟨c,hc,?_⟩
  intro ξPart hξPart hξbound hξdeg hξedges hξcorr d hd hd3 hdlarge hcut Nret hNret hspacing ha hγrate hcutHost
  obtain ⟨Ncor,hNcorpos,hNcor⟩:=hCorr ξPart hξPart.le hξbound d
  obtain ⟨Nbal,hNbal⟩:=supplied_vortex_regular_class_common_to_balanced r k₀ K d hr hK hm hd hd3 hdlarge αRef sstar γRich tstar kstar θ ρ₀ eps lam ζret alpha γ δold δlocal δglobal αMatch bmatch εQ ξ lamAssign ξPart hθpos hθ hρ₀ hρ₀max hcut hα hlam hε hδ hgap hδglobal hθglobal hαsmall hαglobal Nret hNret hbmatch hαb hbd hεsmall hθδ hθlocal hlamlocal hspacing heps hξ hξ0 C₀ hC hehi hlamhi hlamθ hγ ha0 hγε heps1 ha hγrate hζ hζ0 ρscale hρscale hρscale0 hξdeg hξedges hcutHost
  refine ⟨max Ncor Nbal,?_⟩
  intro n hnN U _ _ F hF Allowed hAllowed hclass P Zpart Dpart Bpart mpart hmpart π Dnat vsize βQ Q hreg hDv hρhi hρlo hDlo hDhi hvsize hsize hpres hnoshort hscale hmargin β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel BM BO t₀ Δ τ hτ hΔcorr hfbound hdegree hmin size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr weight w τWeight Asrc hBM hw hBO hw0 hwupper hn hDvR βlist lamList ζList βfinal η γList pstar hn2 hu hεδ hβfinal hβfinal1 hδbound hnβ hnδ hγList hpstar hp hβlist hlamList hζList hΔζ hP herror hlistMargin hlistBudget hsub htrim hout
  have hbalanced:=hNbal n (by omega) U F hF Allowed hAllowed hclass P Zpart Dpart Bpart mpart π Dnat vsize βQ Q hreg hDv hρhi hρlo hDlo hDhi hvsize hsize hpres hnoshort hscale hmargin β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel BM BO t₀ Δ τ hτ size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr weight w τWeight Asrc hBM hw hBO hw0 hwupper hn hDvR βlist lamList ζList βfinal η γList pstar hn2 hu hεδ hβfinal hβfinal1 hδbound hnβ hnδ hγList hpstar hp hβlist hlamList hζList hΔζ hP herror hlistMargin hlistBudget hsub htrim
  have hdecB:suppliedClassCommonToBalancedFin n=suppliedClassCommonSpacingChosenFin n:=Subsingleton.elim _ _
  have hdecBK:suppliedClassCommonToBalancedFin K=suppliedClassCommonSpacingChosenFin K:=Subsingleton.elim _ _
  try rw [hdecB] at hbalanced
  try rw [hdecBK] at hbalanced
  have hcorr:=hNcor r k₀ K hr hK hm hd sstar γRich tstar kstar θ (initialIndexDensity U Dnat) Dnat eps lam ζret alpha γ hθpos hθ hρlo hρhi hDvR hcut β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel BM BO t₀ ξ Δ τ fprot hfprot size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr n (by omega) hn U F hF Allowed hAllowed hsize hclass P Zpart Dpart Bpart mpart π weight w Dnat vsize βQ εQ Q hpres δlocal δglobal αMatch bmatch lamAssign hmpart hfbound hdegree hmin
  have hdecC:suppliedClassFullyUniformCorrectionFin n=suppliedClassCommonSpacingChosenFin n:=Subsingleton.elim _ _
  have hdecCK:suppliedClassFullyUniformCorrectionFin K=suppliedClassCommonSpacingChosenFin K:=Subsingleton.elim _ _
  try rw [hdecC] at hcorr
  try rw [hdecCK] at hcorr
  have hchosen:=supplied_vortex_class_at_chosen_correction r k₀ K d hr hK hm hd αRef sstar γRich tstar kstar θ ρ₀ (initialIndexDensity U Dnat) Dnat eps lam ζret alpha γ hθpos hθ hρ₀ hρlo hρhi hDvR hcut β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel BM BO t₀ ξ Δ τ size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr n hn U F hF Allowed hAllowed hsize hclass P Zpart Dpart Bpart mpart ξPart π weight w Dnat vsize βQ εQ Q hpres δlocal δglobal αMatch bmatch lamAssign δcorr fprot hΔcorr hξcorr
  have hdecA:suppliedClassChosenCorrectionFin n=suppliedClassCommonSpacingChosenFin n:=Subsingleton.elim _ _
  have hdecAK:suppliedClassChosenCorrectionFin K=suppliedClassCommonSpacingChosenFin K:=Subsingleton.elim _ _
  try rw [hdecA] at hchosen
  try rw [hdecAK] at hchosen
  exact hchosen (hcorr (hbalanced hout))
end Oberwolfach
