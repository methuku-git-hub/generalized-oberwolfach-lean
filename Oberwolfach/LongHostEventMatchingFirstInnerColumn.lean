module

public import Oberwolfach.LongHostEventConclusionFirstInnerColumn
public import Oberwolfach.SuppliedVortexOutcomeMatchingFirstInnerColumn
public import Oberwolfach.LongHostFixedSpacingEventConclusionWithStarts
public import Oberwolfach.SuppliedVortexFixedSpacingOutcomeMatchingWithStarts

@[expose] public section
/-! The actual regular-host event, enriched with matching inputs on the same witness. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

def HostVortexFixedSpacingEventConclusionWithFirstInnerColumnMatching
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
:Prop :=
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
    SuppliedVortexFixedSpacingOutcomeWithFirstInnerColumnMatching r k₀ K d hr hK3 hm hd
      αRef sstar γRich tstar kstar θ ρ₀ (initialIndexDensity U Dnat) Dnat eps lam ζret
      hθpos hθ hρ₀ hρlo hρhi hD hcut
      β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel
      BM BO t₀ ξ Δ (τ₀/2) size a₀ b₀ e₀ aRob bRob eRob f₀ (Q.length-1) hNbr n (by omega)
      U F hF Allowed hAllowed hsize hclass P π weight w Dnat vsize βQ εQ Q hpres

theorem host_vortex_fixed_spacing_event_with_first_inner_column_matching
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
    (hout:HostVortexFixedSpacingEventConclusionWithFirstInnerColumn r k₀ Qpow hr hQpow hlen αRef sstar ω γRich tstar kstar hαRef hsstar hsstar1 hω hmargin
      hγRich hγRich1 hγcap htstar htstar1 horder hkstar K hK3 hm θ ρ₀ hθpos hθ hρ₀ hωBound
      ζret hζret ε₀ lam hε₀ hlam hlamθ eps d hd hcut BM hBM BO hBO αHost A hαHost hαmargin htstarBound hkBound):
    HostVortexFixedSpacingEventConclusionWithFirstInnerColumnMatching r k₀ Qpow hr hQpow hlen αRef sstar ω γRich tstar kstar hαRef hsstar hsstar1 hω hmargin
      hγRich hγRich1 hγcap htstar htstar1 horder hkstar K hK3 hm θ ρ₀ hθpos hθ hρ₀ hωBound
      ζret hζret ε₀ lam hε₀ hlam hlamθ eps d hd hcut BM hBM BO hBO αHost A hαHost hαmargin htstarBound hkBound :=by
  unfold HostVortexFixedSpacingEventConclusionWithFirstInnerColumn at hout
  unfold HostVortexFixedSpacingEventConclusionWithFirstInnerColumnMatching
  obtain ⟨β,βCommon,εAbs,εRob,ζRob,δAbs,hβ,hβCommon,hεAbs,hεRob,hζRob,hδAbs,hLate⟩:=hout
  refine ⟨β,βCommon,εAbs,εRob,ζRob,δAbs,hβ,hβCommon,hεAbs,hεRob,hζRob,hδAbs,?_⟩
  intro εRef δRef εQ χ χCommon Qreal pstarRef ζ εBal ζBal χBal εNbr ζNbr χNbr εLoad ζLoad χLoad ζLocal χLocal ζConfig χConfig τLevel
    hεRef hδRef hεQ hεQ1 hεQAbs hχ hχCommon hpstarRef hζ hεBal hζBal hχBal hεNbr hζNbr hχNbr hεLoad hζLoad hχLoad hζLocal hχLocal hζConfig hχConfig hτLevel hQreal hNbr hpstarBound hgap
  obtain ⟨βmax,hβmax,hLate⟩:=hLate εRef δRef εQ χ χCommon Qreal pstarRef ζ εBal ζBal χBal εNbr ζNbr χNbr εLoad ζLoad χLoad ζLocal χLocal ζConfig χConfig τLevel
    hεRef hδRef hεQ hεQ1 hεQAbs hχ hχCommon hpstarRef hζ hεBal hζBal hχBal hεNbr hζNbr hχNbr hεLoad hζLoad hχLoad hζLocal hχLocal hζConfig hχConfig hτLevel hQreal hNbr hpstarBound hgap
  refine ⟨βmax,hβmax,?_⟩
  intro βQ hβQ hβQ1 hβQα hβQmax hβQbal hβQref
  obtain ⟨MLevel,hMLevel,mLevel,hmLevel,η,hη,t₀,τ₀,Δ,ξ,ht₀,hτ₀,hτ₀bound,hΔ,hξ,hξbound,N,vsize,hvsize,hvm,hLate⟩:=
    hLate βQ hβQ hβQ1 hβQα hβQmax hβQbal hβQref
  refine ⟨MLevel,hMLevel,mLevel,hmLevel,η,hη,t₀,τ₀,Δ,ξ,ht₀,hτ₀,hτ₀bound,hΔ,hξ,hξbound,N,vsize,hvsize,hvm,?_⟩
  intro size
  obtain ⟨a₀,b₀,e₀,aRob,bRob,eRob,hLate⟩:=hLate size
  refine ⟨a₀,b₀,e₀,aRob,bRob,eRob,?_⟩
  intro f₀
  obtain ⟨NTotal,hNTotal,hLate⟩:=hLate f₀
  refine ⟨NTotal,hNTotal,?_⟩
  intro Allowed hAllowedSet hvalid n hn U _ _ F hF hAllowed hclass P Dnat hreg hmin hρlo hρhi
  obtain ⟨hD,hsize,Q,π,hpres,hnoshort,w,weight,hout⟩:=
    hLate Allowed hAllowedSet hvalid n hn U F hF hAllowed hclass P Dnat hreg hmin hρlo hρhi
  refine ⟨hD,hsize,Q,π,hpres,hnoshort,w,weight,?_⟩
  exact supplied_vortex_fixed_spacing_outcome_with_first_inner_column_matching r k₀ K d hr hK3 hm hd
    αRef sstar γRich tstar kstar θ ρ₀ (initialIndexDensity U Dnat) Dnat eps lam ζret
    hθpos hθ hρ₀ hρlo hρhi hD hcut
    β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel
    BM BO t₀ ξ Δ (τ₀/2) size a₀ b₀ e₀ aRob bRob eRob f₀ (Q.length-1) hNbr n (by omega)
    U F hF Allowed hAllowed hsize hclass P π weight w Dnat vsize βQ εQ Q hpres hnoshort hout
end Oberwolfach
