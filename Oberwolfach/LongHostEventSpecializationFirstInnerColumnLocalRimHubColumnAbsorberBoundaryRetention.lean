module

public import Oberwolfach.SuppliedVortexEventInnerColumnLocalRimHubColumnAbsorberBoundaryRetention
public import Oberwolfach.LongHostEventConclusionFirstInnerColumnLocalRimHubColumnAbsorberBoundaryRetention
public import Oberwolfach.SuppliedVortexEventInnerColumnLocalRimHub
public import Oberwolfach.LongHostEventConclusionFirstInnerColumnLocalRimHub
public import Oberwolfach.SuppliedVortexEventInnerColumnLocalFamily
public import Oberwolfach.LongHostEventConclusionFirstInnerColumnLocalFamily
public import Oberwolfach.VortexLocalRowSizeConditions
public import Oberwolfach.SuppliedVortexEventInnerColumnRimRow
public import Oberwolfach.LongHostEventConclusionFirstInnerColumnRimRow
public import Oberwolfach.SuppliedVortexEventInnerColumn
public import Oberwolfach.SuppliedVortexOutcomeFirstInnerColumn
public import Oberwolfach.SuppliedVortexFixedSpacingEventWithStarts
public import Oberwolfach.LongSuppliedVortexFixedSpacingOutcomeWithStarts

@[expose] public section
/-! Invoke the supplied-vortex event on the regular-host vortex and weights. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_host_fixed_spacing_event_specialization_with_local_rim_hub_column_absorber_boundary_retention
    (r k₀ Qpow:ℕ) (hr:2≤r) (hQpow:0<Qpow) (hlen:r+4+1=(k₀+2)*2)
    (αRef sstar ω γRich tstar kstar:ℝ)
    (hαRef:0<αRef) (hsstar:0<sstar) (hsstar1:sstar≤1/100) (hω:0<ω)
    (hmargin:successorCycleRatio k₀+αRef/2≤1/2+αRef)
    (hγRich:0<γRich) (hγRich1:γRich≤1/2) (hγcap:γRich≤αRef)
    (htstar:0<tstar) (htstar1:tstar≤1) (horder:tstar≤sstar) (hkstar:0<kstar)
    (K:ℕ) (hK3:3≤K) (hm:7≤(r+4))
    (θ ρ₀:ℝ) (hθpos:0<θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hωBound:4*ω≤ρ₀)
    (ζret:ℝ) (hζret:0<ζret)
    (ε₀ lam:ℝ) (hε₀:ε₀<1) (hlam:0<lam) (hlamθ:lam≤θ)
    (eps:ℝ) (d:ℕ) (hd:2≤d)
    (hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ)
    (BM:ℝ) (hBM:0<BM) (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (αHost A:ℝ) (hαHost:0<αHost) (hαmargin:2*αRef≤αHost)
    (htstarBound:tstar≤(1/100)/(((r+4):ℕ):ℝ))
    (hkBound:∀ρ:ℝ,ρ₀≤ρ→kstar≤ρ*(1/100)/2 ∧ kstar≤ρ*((1/100)/(((r+4):ℕ):ℝ))/2)
    (hHost:HostMatchingVortexContinuation (r+4) K d αHost A BM BO)
    (hEvent:SuppliedVortexFixedSpacingEventWithInnerColumnAndLocalRimHubColumnAbsorberBoundaryRetention r k₀ Qpow hr hQpow hlen
      αRef sstar ω γRich tstar kstar hαRef hsstar hsstar1 hω hmargin hγRich hγRich1 hγcap
      htstar htstar1 horder hkstar K hK3 hm θ ρ₀ hθpos hθ hρ₀ hωBound ζret hζret ε₀ lam hε₀ hlam hlamθ
      eps d hd hcut BM hBM BO hBO) :
    ∃ β βCommon εAbs εRob ζRob δAbs:ℝ,0<β∧0<βCommon∧0<εAbs∧0<εRob∧0<ζRob∧0<δAbs ∧
    ∀ (εRef δRef εQ χ χCommon Qreal pstarRef ζ εBal ζBal χBal εNbr ζNbr χNbr εLoad ζLoad χLoad ζLocal χLocal ζConfig χConfig τLevel:ℝ)
    (hεRef:0<εRef) (hδRef:0<δRef) (hεQ:0<εQ) (hεQ1:εQ<1/4) (hεQAbs:εQ≤εAbs) (hχ:0<χ)
    (hχCommon:0<χCommon) (hpstarRef:0<pstarRef) (hζ:0<ζ) (hεBal:0<εBal) (hζBal:0<ζBal) (hχBal:0<χBal)
    (hεNbr:0<εNbr) (hζNbr:0<ζNbr) (hχNbr:0<χNbr) (hεLoad:0<εLoad)
    (hζLoad:0<ζLoad) (hχLoad:0<χLoad) (hζLocal:0<ζLocal) (hχLocal:0<χLocal) (hζConfig:0<ζConfig) (hχConfig:0<χConfig) (hτLevel:0<τLevel)
    (hQreal:0<Qreal) (hNbr:ℕ) (hpstarBound:4*(((r+4):ℕ):ℝ)*pstarRef≤ρ₀*(1/100))
    (hgap:χ+χCommon+χBal+2*χNbr+χLoad+χLocal+χConfig<ε₀),
    ∃βmax:ℝ,0<βmax ∧ ∀βQ:ℝ,0<βQ→βQ≤1/4→βQ≤αRef/4→βQ≤βmax→βQ≤εBal/4→βQ≤εRef/4→
    ∃MLevel:ℕ,1≤MLevel ∧
    ∃mLevel:ℕ,1≤mLevel ∧ ∃η:ℝ,0<η ∧ ∃t₀ τ₀ Δ ξ:ℝ,0<t₀ ∧ 0<τ₀ ∧ τ₀≤1/16 ∧ 0<Δ ∧ 0<ξ ∧ 4*ξ≤eps/2 ∧ ∃N:ℕ,
    ∃vsize:ℕ,1≤vsize ∧ mLevel≤vsize ∧
    ∀size:ℕ,∃a₀ b₀ e₀ aRob bRob eRob:ℕ,∀f₀:ℕ,∃NTotal:ℕ,∃hNTotal:1≤NTotal,
    ∀Allowed:Set ℕ,Allowed.Nonempty→(∀s∈Allowed,3≤s)→
    ∀n:ℕ,∀hn:NTotal≤n,∀(U:Type) [Fintype U] [DecidableEq U],
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hclass:∀u,factorPreparationClass (F u) K=none)
    (P:SimpleGraph (Fin n)) (Dnat:ℕ) (hreg:P.IsRegularOfDegree Dnat)
    (hmin:(allowedThreshold Allowed+αHost)*n≤(Dnat:ℝ))
    (hρlo:ρ₀ ≤ initialIndexDensity U Dnat) (hρhi:initialIndexDensity U Dnat≤1),
    ∃hD:0<(Dnat:ℝ),
    ∃hsize:initialIndexDensity U Dnat*(Dnat:ℝ)=2*Fintype.card U,
    ∃Q:Vortex U P Dnat βQ εQ vsize,∃π:Equiv.Perm (Fin n),
    ∃hpres:(∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
    (∀x l,0<l→l<2*d+1→(π^l) x≠x) ∧
    ∃w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ,
    ∃weight:(Fin ((r+4)+1)→Fin n)→ℝ,
    SuppliedVortexFixedSpacingOutcomeWithFirstInnerColumnAndLocalRimHubColumnAbsorberBoundaryRetention r k₀ K d hr hK3 hm hd
      αRef sstar γRich tstar kstar θ ρ₀ (initialIndexDensity U Dnat) Dnat eps lam ζret
      hθpos hθ hρ₀ hρlo hρhi hD hcut
      β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel
      BM BO t₀ ξ Δ (τ₀/2) size a₀ b₀ e₀ aRob bRob eRob f₀ (Q.length-1) hNbr n (by omega)
      U F hF Allowed hAllowed hsize hclass P π weight w Dnat vsize βQ εQ Q hpres := by
  obtain ⟨β,βCommon,εAbs,εRob,ζRob,δAbs,hβ,hβCommon,hεAbs,hεRob,hζRob,hδAbs,hLate⟩:=hEvent
  refine ⟨β,βCommon,εAbs,εRob,ζRob,δAbs,hβ,hβCommon,hεAbs,hεRob,hζRob,hδAbs,?_⟩
  intro εRef δRef εQ χ χCommon Qreal pstarRef ζ εBal ζBal χBal εNbr ζNbr χNbr εLoad ζLoad χLoad ζLocal χLocal ζConfig χConfig τLevel
    hεRef hδRef hεQ hεQ1 hεQAbs hχ hχCommon hpstarRef hζ hεBal hζBal hχBal hεNbr hζNbr hχNbr hεLoad hζLoad hχLoad hζLocal hχLocal hζConfig hχConfig hτLevel hQreal hNbr hpstarBound hgap
  obtain ⟨βmax,hβmax,hLate⟩:=hLate εRef δRef εQ χ χCommon Qreal pstarRef ζ εBal ζBal χBal εNbr ζNbr χNbr εLoad ζLoad χLoad ζLocal χLocal ζConfig χConfig τLevel
    hεRef hδRef hεQ hεQ1 hεQAbs hχ hχCommon hpstarRef hζ hεBal hζBal hχBal hεNbr hζNbr hχNbr hεLoad hζLoad hχLoad hζLocal hχLocal hζConfig hχConfig hτLevel hQreal hNbr hpstarBound hgap
  refine ⟨βmax,hβmax,?_⟩
  intro βQ hβQ hβQ1 hβQα hβQmax hβQbal hβQref
  let Cscale:ℝ:=2/εQ
  let δrow:ℝ:=(1-ε₀)/1024
  let δhub:ℝ:=(ε₀-(χ+χCommon+χBal+2*χNbr+χLoad+χLocal+χConfig))/8
  let δcol:ℝ:=(ε₀-(χ+χCommon+χBal+2*χNbr+χLoad+χLocal+χConfig))/8
  let δocc:ℝ:=(ε₀-(χ+χCommon+χBal+2*χNbr+χLoad+χLocal+χConfig))/8
  let δbd:ℝ:=(ε₀-(χ+χCommon+χBal+2*χNbr+χLoad+χLocal+χConfig))/16
  let δret:ℝ:=(ε₀-(χ+χCommon+χBal+2*χNbr+χLoad+χLocal+χConfig))/32
  have hδret:0<δret:=by dsimp [δret];linarith only [hgap]
  have hδbd:0<δbd:=by dsimp [δbd];linarith only [hgap]
  have hδocc:0<δocc:=by dsimp [δocc];linarith only [hgap]
  have hδhub:0<δhub:=by dsimp [δhub];linarith only [hgap]
  have hδcol:0<δcol:=by dsimp [δcol];linarith only [hgap]
  have hδhubgap:δhub+δcol+δocc+δbd+δret≤(ε₀-(χ+χCommon+χBal+2*χNbr+χLoad+χLocal+χConfig))/2:=by dsimp [δhub,δcol,δocc,δbd,δret];linarith only [hgap]
  have hCscale:0≤Cscale:=by dsimp [Cscale];positivity
  have hδrow:0<δrow:=by dsimp [δrow];linarith only [hε₀]
  have hδbound:δrow≤(1-ε₀)/512:=by dsimp [δrow];linarith only [hε₀]
  obtain ⟨MLevel,hMLevel,mLevelOld,hmLevelOld,η,hη,t₀,τ₀,Δ,ξ,ht₀,hτ₀,hτ₀bound,hΔ,hξ,hξbound,N,hAll⟩:=
    hLate βQ hβQ.le hβQ1 hβQα hβQmax hβQbal hβQref Cscale δrow δhub δcol δocc δbd δret hCscale hδrow hδbound hδhub hδcol hδocc hδbd hδret hδhubgap
  let threshold:=localRowBudgetThreshold Cscale δrow hCscale hδrow
  let thresholdHub:=retainedUnassignedHubThreshold d hd (1/2) δhub (by norm_num) hδhub
  let thresholdCol:=retainedUnassignedColumnThreshold d hd δcol hδcol
  let thresholdOcc:=retainedAbsorberOccurrenceThreshold d hd δocc hδocc
  let thresholdBd:=retainedBoundaryHubsThreshold d hd δbd hδbd
  let thresholdRet:=rawMarkedLocalRetentionThreshold d hd (ρ₀/(400*(((r+4):ℕ):ℝ))) ζret (ρ₀/8) δret (by positivity) hζret (by positivity) hδret
  let thresholdBoth:=max (max (max (max threshold (max thresholdHub thresholdCol)) thresholdOcc) thresholdBd) thresholdRet
  obtain ⟨mBound,hmBound⟩:=exists_nat_gt (2*(thresholdBoth:ℝ)/εQ)
  let mLevel:=max mLevelOld (max mBound 1)
  have hmLevel:1≤mLevel:=by dsimp [mLevel];omega
  have hOld:mLevelOld≤mLevel:=by dsimp [mLevel];omega
  have hBound:mBound≤mLevel:=by dsimp [mLevel];omega
  have hthresholdBoth:(thresholdBoth:ℝ)≤εQ*mLevel/2:=by
    have hb:(2*(thresholdBoth:ℝ)/εQ)<mLevel:=lt_of_lt_of_le hmBound (by exact_mod_cast hBound)
    have hh:2*(thresholdBoth:ℝ)<(mLevel:ℝ)*εQ:=(div_lt_iff₀ hεQ).1 hb
    nlinarith only [hh]
  have hthreshold:(threshold:ℝ)≤εQ*mLevel/2:=by
    have hh:(threshold:ℝ)≤thresholdBoth:=by exact_mod_cast (le_trans (le_trans (le_trans (le_max_left threshold (max thresholdHub thresholdCol)) (le_max_left _ thresholdOcc)) (le_max_left _ thresholdBd)) (le_max_left _ thresholdRet))
    exact hh.trans hthresholdBoth
  have hthresholdHub:(thresholdHub:ℝ)≤εQ*mLevel/2:=by
    have hh:(thresholdHub:ℝ)≤thresholdBoth:=by exact_mod_cast (le_trans (le_trans (le_trans (le_trans (le_max_left thresholdHub thresholdCol) (le_max_right threshold (max thresholdHub thresholdCol))) (le_max_left _ thresholdOcc)) (le_max_left _ thresholdBd)) (le_max_left _ thresholdRet))
    exact hh.trans hthresholdBoth
  have hthresholdCol:(thresholdCol:ℝ)≤εQ*mLevel/2:=by
    have hh:(thresholdCol:ℝ)≤thresholdBoth:=by exact_mod_cast (le_trans (le_trans (le_trans (le_trans (le_max_right thresholdHub thresholdCol) (le_max_right threshold (max thresholdHub thresholdCol))) (le_max_left _ thresholdOcc)) (le_max_left _ thresholdBd)) (le_max_left _ thresholdRet))
    exact hh.trans hthresholdBoth
  have hthresholdOcc:(thresholdOcc:ℝ)≤εQ*mLevel/2:=by
    have hh:(thresholdOcc:ℝ)≤thresholdBoth:=by exact_mod_cast (le_trans (le_trans (le_max_right _ thresholdOcc) (le_max_left _ thresholdBd)) (le_max_left _ thresholdRet))
    exact hh.trans hthresholdBoth
  have hthresholdBd:(thresholdBd:ℝ)≤εQ*mLevel/2:=by
    have hh:(thresholdBd:ℝ)≤thresholdBoth:=by exact_mod_cast (le_trans (le_max_right _ thresholdBd) (le_max_left _ thresholdRet))
    exact hh.trans hthresholdBoth
  have hthresholdRet:(thresholdRet:ℝ)≤εQ*mLevel/2:=by
    have hh:(thresholdRet:ℝ)≤thresholdBoth:=by exact_mod_cast (le_max_right _ thresholdRet)
    exact hh.trans hthresholdBoth
  obtain ⟨vsize,hvsize,hvm,hHost⟩:=hHost βQ εQ ρ₀ hβQ hεQ hεQ1 hρ₀ mLevel
  obtain ⟨N0,hN0,hHost⟩:=hHost (τ₀/2) (by positivity)
  refine ⟨MLevel,hMLevel,mLevel,hmLevel,η,hη,t₀,τ₀,Δ,ξ,ht₀,hτ₀,hτ₀bound,hΔ,hξ,hξbound,N,vsize,hvsize,hvm,?_⟩
  intro size
  obtain ⟨a₀,b₀,e₀,aRob,bRob,eRob,hAll⟩:=hAll size
  refine ⟨a₀,b₀,e₀,aRob,bRob,eRob,?_⟩
  intro f₀
  obtain ⟨NHost,hAll⟩:=hAll f₀
  let NTotal:=max (max (max (max N NHost) 1) N0) (2*vsize)
  refine ⟨NTotal,by dsimp [NTotal];omega,?_⟩
  intro Allowed hAllowedSet hvalid n hn U _ _ F hF hAllowed hclass P Dnat hreg hmin hρlo hρhi
  have hnEvent:max (max N NHost) 1≤n:=by dsimp [NTotal] at hn;omega
  have hnHost:max N0 (2*vsize)≤n:=by dsimp [NTotal] at hn;omega
  obtain ⟨Q,π,hpres,hnoshort,hUn,hDnat,hD,hDlo,hDhi,hDmargin,hsize,hdeg,hv2,hQL,w,weight,hwBounds,he,hbudget,hw⟩:=
    hHost Allowed hAllowedSet hvalid n hnHost U F hF hAllowed θ hθpos hθ hcut hclass P Dnat hreg hmin hρlo hρhi
  have hmarginHost:(1/2+2*αRef)*n≤(Dnat:ℝ):=by
    have hnnonneg:0≤(n:ℝ):=by positivity
    nlinarith
  have hw0:∀i C,0≤w i C:=fun i C=>(hwBounds i C).1
  have hwupper:∀i C,w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i):=fun i C=>(hwBounds i C).2
  have hbudgetV:∀i∈longRetainedSeedIndices F hF K θ,
      6*((longPaddedSeedExponent i+2:ℕ):ℝ)^4*BO i*(2*(3*d))+(0:ℝ)*n≤(τ₀/2)*Dnat:=by
    intro i hi
    simpa using (hbudget i hi).2
  have hbudgetE:∀i∈longRetainedSeedIndices F hF K θ,
      5*((longPaddedSeedExponent i+2:ℕ):ℝ)^4*BO i*(2*(3*d))/n≤τ₀/2:=by
    intro i hi
    exact (hbudget i hi).1
  have hL:Q.length-1<Q.length:=by omega
  obtain ⟨hk1,hk2⟩:=hkBound (initialIndexDensity U Dnat) hρlo
  let Tlevel:=Finset.Icc 1 Q.length
  have hthresholdV:(threshold:ℝ)≤εQ*vsize/2:=by
    have hv:(mLevel:ℝ)≤vsize:=by exact_mod_cast hvm
    have hh:=mul_le_mul_of_nonneg_left hv hεQ.le
    linarith only [hthreshold,hh]
  have hthresholdHubV:(thresholdHub:ℝ)≤εQ*vsize/2:=by
    have hv:(mLevel:ℝ)≤vsize:=by exact_mod_cast hvm
    have hh:=mul_le_mul_of_nonneg_left hv hεQ.le
    linarith only [hthresholdHub,hh]
  have hthresholdColV:(thresholdCol:ℝ)≤εQ*vsize/2:=by
    have hv:(mLevel:ℝ)≤vsize:=by exact_mod_cast hvm
    have hh:=mul_le_mul_of_nonneg_left hv hεQ.le
    linarith only [hthresholdCol,hh]
  have hthresholdOccV:(thresholdOcc:ℝ)≤εQ*vsize/2:=by
    have hv:(mLevel:ℝ)≤vsize:=by exact_mod_cast hvm
    have hh:=mul_le_mul_of_nonneg_left hv hεQ.le
    linarith only [hthresholdOcc,hh]
  have hthresholdBdV:(thresholdBd:ℝ)≤εQ*vsize/2:=by
    have hv:(mLevel:ℝ)≤vsize:=by exact_mod_cast hvm
    have hh:=mul_le_mul_of_nonneg_left hv hεQ.le
    linarith only [hthresholdBd,hh]
  have hthresholdRetV:(thresholdRet:ℝ)≤εQ*vsize/2:=by
    have hv:(mLevel:ℝ)≤vsize:=by exact_mod_cast hvm
    have hh:=mul_le_mul_of_nonneg_left hv hεQ.le
    linarith only [hthresholdRet,hh]
  have hminRet:∀i∈Tlevel,thresholdRet≤(Q.extendedVertices i).card:=by
    intro i hi
    exact Q.extended_card_at_least_threshold hthresholdRetV (Finset.mem_Icc.mp hi).2
  have hminBd:∀i∈Tlevel,thresholdBd≤(Q.extendedVertices i).card:=by
    intro i hi
    exact Q.extended_card_at_least_threshold hthresholdBdV (Finset.mem_Icc.mp hi).2
  have hminOcc:∀i∈Tlevel,thresholdOcc≤(Q.extendedVertices i).card:=by
    intro i hi
    exact Q.extended_card_at_least_threshold hthresholdOccV (Finset.mem_Icc.mp hi).2
  have hminCol:∀i∈Tlevel,thresholdCol≤(Q.extendedVertices i).card:=by
    intro i hi
    exact Q.extended_card_at_least_threshold hthresholdColV (Finset.mem_Icc.mp hi).2
  have hminHub:∀i∈Tlevel,thresholdHub≤(Q.extendedVertices i).card:=by
    intro i hi
    exact Q.extended_card_at_least_threshold hthresholdHubV (Finset.mem_Icc.mp hi).2
  have hHlevel:∀i∈Tlevel,((Q.extendedIndices i).card:ℝ)≤(1/2:ℝ)*(Q.extendedVertices i).card:=by
    intro i hi
    have hDn:0<Dnat:=by exact_mod_cast hD
    have hh:=Q.extended_index_size_upper hreg (by simpa only [Fintype.card_fin] using (show 0<n by omega)) hDn hεQ.le hρhi i
    have hhR:(2:ℝ)*(Q.extendedIndices i).card≤(Q.extendedVertices i).card:=by exact_mod_cast hh
    linarith only [hhR]
  have hminLevel:∀i∈Tlevel,threshold≤(Q.extendedVertices i).card:=by
    intro i hi
    have hiL:i≤Q.length:=(Finset.mem_Icc.mp hi).2
    exact Q.extended_card_at_least_threshold hthresholdV hiL
  have hposLevel:∀i∈Tlevel,1≤(Q.extendedVertices i).card:=by
    intro i hi
    exact le_trans (localRowBudgetThreshold_spec Cscale δrow hCscale hδrow).1 (hminLevel i hi)
  have hinjLevel:=Q.extended_card_injOn_positive hεQ.le (le_of_lt hεQ1) Tlevel hposLevel
  have hBlevel:∀i∈Tlevel,((Q.extendedVertices (i-1)).card:ℝ)≤Cscale*(Q.extendedVertices i).card:=by
    intro i hi
    obtain ⟨hi1,hiL⟩:=Finset.mem_Icc.mp hi
    exact Q.extended_previous_card_le hεQ hi1 hiL (hposLevel i hi)
  have hJA:∀i∈Tlevel,(Q.extendedIndices i).card≤(Q.extendedVertices i).card:=by
    intro i hi
    have hnR:(0:ℝ)≤(Q.extendedVertices i).card:=Nat.cast_nonneg _
    have hh:=hHlevel i hi
    have hhR:((Q.extendedIndices i).card:ℝ)≤(Q.extendedVertices i).card:=by linarith only [hh,hnR]
    exact_mod_cast hhR
  have hHlo:∀i∈Tlevel,(ρ₀/8)*((Q.extendedVertices i).card:ℝ)≤(Q.extendedIndices i).card:=by
    intro i hi
    have hiL:i≤Q.length:=(Finset.mem_Icc.mp hi).2
    have hDN:(Fintype.card (Fin n):ℝ)/2≤Dnat:=by simpa only [Fintype.card_fin] using hDlo
    have hh:=Q.index_size_lower hreg (by simpa only [Fintype.card_fin] using (show 0<n by omega)) hDN hρ₀ hρlo hβQ.le hβQ1 hiL
    simpa only [Q.extendedVertices_eq hiL,Q.extendedIndices_eq hiL] using hh
  have hInvLevel:∀i∈Tlevel,∀x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i:=by
    intro i hi x
    exact hpres i x
  have hJpos:∀i∈Tlevel,0<(Q.extendedIndices i).card:=by
    intro i hi
    have hiL:i≤Q.length:=(Finset.mem_Icc.mp hi).2
    have hp:0<(Q.vertices i).card:=by
      rw [← Q.extendedVertices_eq hiL]
      exact lt_of_lt_of_le (by omega : 0<1) (hposLevel i hi)
    have hpR:(0:ℝ)<(Q.vertices i).card:=by exact_mod_cast hp
    have hDN:(Fintype.card (Fin n):ℝ)/2≤Dnat:=by simpa only [Fintype.card_fin] using hDlo
    have hh:=Q.index_size_lower hreg (by simpa only [Fintype.card_fin] using (show 0<n by omega)) hDN hρ₀ hρlo hβQ.le hβQ1 hiL
    have hprod:0<ρ₀/8*(Q.vertices i).card:=by positivity
    have hhpos:(0:ℝ)<(Q.indices i).card:=lt_of_lt_of_le hprod hh
    rw [Q.extendedIndices_eq hiL]
    exact_mod_cast hhpos
  have hvmOld:mLevelOld≤vsize:=le_trans hOld hvm
  have hout:=hAll n hnEvent U F hF Allowed hAllowed (initialIndexDensity U Dnat) Dnat
    hρlo hρhi hD hsize hclass P π (τ₀/2) A weight hw hDlo hDhi w hw0 hwupper hUn hnoshort (Q.extendedVertices 1) ℕ Tlevel (fun i=>Q.extendedVertices i)
    (fun i=>Q.extendedVertices (i-1)) (fun i=>Q.extendedIndices i) hminCol hminOcc hminBd hminRet hHlo hInvLevel hJpos hJA hminHub hHlevel hminLevel hinjLevel hBlevel 0
    he hdeg hbudgetV hbudgetE (by positivity) (by linarith) hδAbs.le
    Dnat vsize rfl rfl hreg hmarginHost hvmOld Q hpres (Q.length-1) hL hk1 hk2 htstarBound
  exact ⟨hD,hsize,Q,π,hpres,hnoshort,w,weight,hout⟩
end Oberwolfach
