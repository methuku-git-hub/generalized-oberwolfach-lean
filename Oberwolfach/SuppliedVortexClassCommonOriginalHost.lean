module

public import Oberwolfach.TwoComponentLower
public import Oberwolfach.BinaryClassMultiplicity
public import Oberwolfach.FirstVortexListThresholdWithSize
public import Oberwolfach.RegularHostFirstMatchingInputs
public import Oberwolfach.FirstVortexHostScaleToInner
public import Oberwolfach.SuppliedVortexRegularBoundaryDeletionCap
public import Oberwolfach.SuppliedVortexClassCommonChosenLateRates
public import Oberwolfach.SuppliedVortexClassCommonToChosenUniformSpacing
public import Oberwolfach.FirstVortexClassDualDeletionBudgets
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
local instance suppliedClassCommonOriginalHostFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem supplied_vortex_regular_class_common_original_host
    (r k₀ K:ℕ) (hr:2≤r) (hK:3≤K) (hm:7≤r+4)
    (αRef sstar γRich tstar kstar θ ρ₀ eps lam ζret:ℝ)
    (δold δlocal δglobal αMatch bmatch εQ ξ lamAssign Δ:ℝ) (Bpart:ℕ) (hαRef:0<αRef) (αHost:ℝ) (hαmargin:αRef≤αHost) (hΔ:0<Δ) (hξpos:0<ξ) (hlamAssign:lam<lamAssign)
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
    (heps1:eps≤1)
    (hζ:ζret≤θ/4096) (hζ0:0≤ζret) (ρscale:ℝ) (hρscale:ρscale≤θ/4096) (hρscale0:0≤ρscale)
    (βlist lamList ζList βfinal γList:ℝ)
    (hεδ:εQ≤δglobal) (hβfinal:0<βfinal) (hβfinal1:βfinal≤1)
    (hδbound:δglobal≤(βfinal/100)^2) (hγList:0≤γList) (hγListα:γList≤αRef)
    (hβlist:0≤βlist) (hlamList:0≤lamList) (hζList:0<ζList)
    (htrim:βfinal+εQ≤lamList)
:
    ∃δcorr:ℝ,0<δcorr ∧ ∃c:ℝ,0<c ∧ ∃ξPart:ℝ,0<ξPart ∧
    ξPart+δcorr≤(min Δ ζList) ∧ ξPart+δcorr≤ξ ∧
    ξPart≤(2*αMatch)/32 ∧ ξPart/2≤(lamAssign-lam)*εQ ∧
    ∀(d:ℕ) (hd:2≤d) (hd3:3≤d) (hdlarge:(r+4)+2≤d)
    (hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ)
    (Nret:ℕ) (hNret:∀n:ℕ,Nret≤n→∀q errOrd:ℝ,
      q≤1/((((r+4):ℕ):ℝ)+1)→errOrd≤θ*n→
      (n:ℝ)*q/d+(((((r+4)+1)*d-1:ℕ):ℝ))*(2*((n:ℝ)^(3/4:ℝ)/d)+ζret*n)+errOrd≤4*θ*n)
    (hspacing:1/(d:ℝ)≤θ/1024)
    (alpha γ:ℝ) (hγ:0≤γ) (ha0:0≤alpha) (hγε:γ≤eps)
    (ha:alpha≤lam/(10*d)) (hγrate:γ≤lam/(10*d))
    (hcutHost:5/(((((r+4):ℕ):ℝ)+1)*(d:ℝ)+5)+((((r+4):ℕ):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2)
    (Nlist:ℕ) (hList:∀n≥Nlist,
      (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γList*(ρ₀/200)^2*n ∧
      βlist*n+(n:ℝ)^(3/4:ℝ)≤γList*(ρ₀/200)^2*n*(1/100:ℝ) ∧
      (lamList+2*ζList)*n≤βlist*n),
    ∃N:ℕ,∀n:ℕ,N≤n→∀(U:Type) [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowedSet:Allowed.Nonempty) (hvalid:∀r∈Allowed,3≤r) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hclass:∀u,factorPreparationClass (F u) K=none)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (Dnat vsize:ℕ) (βQ:ℝ) (Q:Vortex U P Dnat βQ εQ vsize)
    (hreg:P.IsRegularOfDegree Dnat) (hρhi:initialIndexDensity U Dnat≤1)
    (hρlo:ρ₀ ≤ initialIndexDensity U Dnat) (hDlo:(n:ℝ)/2≤Dnat) (hDhi:(Dnat:ℝ)≤2*n) (hvsize:0<vsize)
    (hsize:initialIndexDensity U Dnat*(Dnat:ℝ)=2*Fintype.card U)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (hscale:∀(N A:ℕ), εQ*N/2≤A→max alpha γ*N≤ρscale*A ∧
      2*(max alpha γ*N)≤δold*A/4)
    (β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel:ℝ)
    (BM:ℝ) (BO:Fin K→ℝ) (t₀ τ:ℝ) (hτ:0≤τ)
    (hminOriginal:(allowedThreshold Allowed+αHost)*(n:ℝ)≤Dnat)
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
      BM BO t₀ ξ Δ τ size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr n hn U F hF Allowed hAllowed hsize hclass P ⊥ Dnat Bpart (binaryClassMultiplicity Dnat (Fintype.card U)) ξPart π weight w Dnat vsize βQ εQ Q hpres →
    SuppliedVortexClassAtChosenCorrection r k₀ K d hr hK hm hd αRef sstar γRich tstar kstar θ ρ₀ (initialIndexDensity U Dnat) Dnat eps lam ζret alpha γ
      hθpos hθ hρ₀ hρlo hρhi hDvR hcut β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel
      BM BO t₀ ξ (min Δ ζList) τ size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr n hn U F hF Allowed hAllowed hsize hclass P ⊥ Dnat Bpart (binaryClassMultiplicity Dnat (Fintype.card U)) ξPart π weight w Dnat vsize βQ εQ Q hpres δlocal δglobal αMatch bmatch lamAssign δcorr Bpart :=by
  have hΔcap:0<min Δ ζList:=lt_min hΔ hζList
  have hΔfloor:min Δ ζList≤Δ:=min_le_left _ _
  have hΔζ:min Δ ζList≤ζList:=min_le_right _ _
  obtain ⟨δcorr,hδcorr,hchoose⟩:=first_vortex_class_dual_deletion_budgets αRef (2*αMatch) ρ₀ εQ (min Δ ζList) ξ δold δlocal lamAssign lam hαRef (by positivity) hρ₀ hε hΔcap hξpos hgap hlamAssign
  obtain ⟨c,hc,hN⟩:=supplied_vortex_regular_class_common_to_chosen_late_rates r k₀ K hr hK hm αRef sstar γRich tstar kstar θ ρ₀ eps lam ζret δold δlocal δglobal αMatch bmatch εQ ξ lamAssign δcorr Bpart hαRef hδcorr (by positivity) hθpos hθ hρ₀ hρ₀max hα hlam hε hδ hgap hδglobal hθglobal hαsmall hαglobal hbmatch hαb hbd hεsmall hθδ hθlocal hlamlocal heps hξ hξ0 C₀ hC hehi hlamhi hlamθ heps1 hζ hζ0 ρscale hρscale hρscale0
  obtain ⟨ξPart,hξPart,hΔbudget,hξbudget,hbound,hξdeg,hξedges,hload⟩:=hchoose c hc
  refine ⟨δcorr,hδcorr,c,hc,ξPart,hξPart,?_,?_,hξdeg,hξedges,?_⟩
  · linarith
  · linarith
  intro d hd hd3 hdlarge hcut Nret hNret hspacing alpha γ hγ ha0 hγε ha hγrate hcutHost Nlist hList
  have hN':=hN ξPart hξPart hbound hξdeg hξedges (by linarith) d hd hd3 hdlarge hcut Nret hNret hspacing alpha γ hγ ha0 hγε ha hγrate hcutHost
  have hdec:suppliedClassCommonLateRatesChosenFin=suppliedClassCommonOriginalHostFin:=by funext n;exact Subsingleton.elim _ _
  try rw [hdec] at hN'
  obtain ⟨N,hN'⟩:=hN'
  have hcoef:0<αRef*(ρ₀/200)^2/16:=by positivity
  obtain ⟨Nprot,hprot⟩:=exists_nat_gt ((Bpart:ℝ)/(αRef*(ρ₀/200)^2/16))
  obtain ⟨Nsize,hsizeList⟩:=first_vortex_list_threshold_with_size d γList (ρ₀/200) βlist lamList ζList βfinal δglobal Nlist hList
  refine ⟨max (max N Nsize) Nprot,?_⟩
  intro n hnN U _ _ F hF Allowed hAllowedSet hvalid hAllowed hclass P π Dnat vsize βQ Q hreg hρhi hρlo hDlo hDhi hvsize hsize hpres hnoshort hscale β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel BM BO t₀ τ hτ hminOriginal size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr weight w τWeight Asrc hBM hw hBO hw0 hwupper hn hDvR hout
  have hnBase:N≤n:=by omega
  have hnSize:Nsize≤n:=by omega
  have hnProt:(Nprot:ℝ)≤n:=by exact_mod_cast (show Nprot≤n by omega)
  have hfbound:(Bpart:ℝ)≤(αRef*(ρ₀/200)^2/16)*n:=by
    have hh: (Bpart:ℝ)<(n:ℝ)*(αRef*(ρ₀/200)^2/16):=
      (div_lt_iff₀ hcoef).mp (lt_of_lt_of_le hprot hnProt)
    nlinarith
  obtain ⟨hn2,hnβ,hnδ,herror,hlistMargin,hlistBudget⟩:=hsizeList n hnSize
  have hhalf:1/2≤allowedThreshold Allowed:=allowedThreshold_half_le hAllowedSet hvalid
  have hminHost:(1/2+αRef)*(n:ℝ)≤Dnat:=by
    have hh:(1/2+αRef:ℝ)≤allowedThreshold Allowed+αHost:=by linarith
    exact (mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg n)).trans hminOriginal
  obtain ⟨hDv,hu,hp,hdegree,hP⟩:=regular_host_first_matching_inputs P ρ₀ (initialIndexDensity U Dnat) αRef γList hreg hDvR hρlo hρhi hsize hDhi hminHost hγListα
  have hmin:∀v,(1/2+αRef)*(n:ℝ)≤P.degree v:=by intro v; rw [hdegree v]; exact hminHost
  have hpstar:0≤ρ₀/200:=by positivity
  have hinnerScale: max alpha γ*n≤ρscale*(Q.extendedVertices 1).card:=
    (first_vortex_host_scale_to_inner Q hε hvsize hscale).1
  have hmargin:=hload n U P Dnat vsize βQ Q hvsize
  have hsmall:=supplied_vortex_regular_boundary_outcome_deletion_cap r k₀ K d hr hK hm hd αRef sstar γRich tstar kstar θ ρ₀ (initialIndexDensity U Dnat) Dnat eps lam ζret alpha γ
    hθpos hθ hρ₀ hρlo hρhi hDvR hcut β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel
    BM BO t₀ ξ Δ (min Δ ζList) τ size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr n hn U F hF Allowed hAllowed hsize hclass
    P ⊥ Dnat Bpart (binaryClassMultiplicity Dnat (Fintype.card U)) ξPart π weight w Dnat vsize βQ εQ Q hpres hΔfloor hout
  have hΔcorr:ξPart+δcorr≤(min Δ ζList):=by linarith
  exact hN' n hnBase U F hF Allowed hAllowed hclass P ⊥ Dnat Bpart (binaryClassMultiplicity Dnat (Fintype.card U)) (by rfl) π Dnat vsize βQ Q hreg hDv hρhi hρlo hDlo hDhi hvsize hsize hpres hnoshort hinnerScale hmargin β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel BM BO t₀ (min Δ ζList) τ hτ hΔcorr hfbound hdegree hmin size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr weight w τWeight Asrc hBM hw hBO hw0 hwupper hn hDvR βlist lamList ζList βfinal γList (ρ₀/200) hn2 hu hεδ hβfinal hβfinal1 hδbound hnβ hnδ hγList hpstar hp hβlist hlamList hζList.le hΔζ hP herror hlistMargin hlistBudget htrim hsmall
end Oberwolfach
