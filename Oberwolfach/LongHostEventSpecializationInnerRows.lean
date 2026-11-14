module

public import Oberwolfach.SuppliedVortexEventInnerRows
public import Oberwolfach.SuppliedVortexOutcomeInnerRows
public import Oberwolfach.SuppliedVortexFixedSpacingEventWithStarts
public import Oberwolfach.LongSuppliedVortexFixedSpacingOutcomeWithStarts

@[expose] public section
/-! Invoke the supplied-vortex event on the regular-host vortex and weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_host_fixed_spacing_event_specialization_with_inner_rows
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
    (hEvent:SuppliedVortexFixedSpacingEventWithInnerRows r k₀ Qpow hr hQpow hlen
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
    SuppliedVortexFixedSpacingOutcomeWithInnerRows r k₀ K d hr hK3 hm hd
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
  obtain ⟨MLevel,hMLevel,mLevel,hmLevel,η,hη,t₀,τ₀,Δ,ξ,ht₀,hτ₀,hτ₀bound,hΔ,hξ,hξbound,N,hAll⟩:=
    hLate βQ hβQ.le hβQ1 hβQα hβQmax hβQbal hβQref
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
  have hout:=hAll n hnEvent U F hF Allowed hAllowed (initialIndexDensity U Dnat) Dnat
    hρlo hρhi hD hsize hclass P π (τ₀/2) A weight hw hDlo hDhi w hw0 hwupper hUn hnoshort (Q.vertices Q.length) 0
    he hdeg hbudgetV hbudgetE (by positivity) (by linarith) hδAbs.le
    Dnat vsize rfl rfl hreg hmarginHost hvm Q hpres (Q.length-1) hL hk1 hk2 htstarBound
  exact ⟨hD,hsize,Q,π,hpres,hnoshort,w,weight,hout⟩
end Oberwolfach
