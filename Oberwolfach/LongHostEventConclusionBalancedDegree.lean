module

public import Oberwolfach.SuppliedVortexOutcomeBalancedDegree
public import Oberwolfach.SuppliedVortexOutcomeFirstInnerColumnLocalRetentionMatchingRates
public import Oberwolfach.SuppliedVortexOutcomeFirstInnerColumnLocalRimHubColumnAbsorberBoundaryRetention
public import Oberwolfach.SuppliedVortexOutcomeFirstInnerColumnLocalRimHub
public import Oberwolfach.SuppliedVortexOutcomeFirstInnerColumnLocalFamily
public import Oberwolfach.SuppliedVortexOutcomeFirstInnerColumnRimRow
public import Oberwolfach.SuppliedVortexOutcomeFirstInnerColumn
public import Oberwolfach.LongHostFixedSpacingEventSpecializationWithStarts

@[expose] public section
/-! The exact regular-host event conclusion, named so the shared choices
can be composed with its checked specialization. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

def HostVortexFixedSpacingEventConclusionWithBalancedDegree
    (r k₀ Qpow:ℕ) (hr:2≤r) (hQpow:0<Qpow) (hlen:r+4+1=(k₀+2)*2)
    (αRef sstar ω γRich tstar kstar:ℝ)
    (hαRef:0<αRef) (hsstar:0<sstar) (hsstar1:sstar≤1/100) (hω:0<ω)
    (hmargin:successorCycleRatio k₀+αRef/2≤1/2+αRef)
    (hγRich:0<γRich) (hγRich1:γRich≤1/2) (hγcap:γRich≤αRef)
    (htstar:0<tstar) (htstar1:tstar≤1) (horder:tstar≤sstar) (hkstar:0<kstar)
    (K:ℕ) (hK3:3≤K) (hm:7≤(r+4))
    (θ ρ₀:ℝ) (hθpos:0<θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hωBound:4*ω≤ρ₀)
    (ζret:ℝ) (hζret:0<ζret)
    (d:ℕ) (hd:2≤d)
    (hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ)
    (BM:ℝ) (hBM:0<BM) (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (αHost A:ℝ) (hαHost:0<αHost) (hαmargin:2*αRef≤αHost)
    (htstarBound:tstar≤(1/100)/(((r+4):ℕ):ℝ))
    (hkBound:∀ρ:ℝ,ρ₀≤ρ→kstar≤ρ*(1/100)/2 ∧ kstar≤ρ*((1/100)/(((r+4):ℕ):ℝ))/2)
:Prop :=
    ∃ β βCommon εAbs εRob ζRob δAbs:ℝ,0<β∧0<βCommon∧0<εAbs∧0<εRob∧0<ζRob∧0<δAbs ∧
    ∀ (εtarget δ ε₀ lam:ℝ) (hεtarget:0<εtarget) (hδ:0<δ) (hε₀:ε₀<1) (hLamPos:0<lam) (hlamθ:lam≤θ),
    ∃ρ eps alpha γ:ℝ,0<ρ ∧ ρ≤θ/4096 ∧
      0<eps ∧ eps≤1 ∧ 3*eps≤lam*(θ/(100*(K:ℝ)^2)) ∧
      0<alpha ∧ alpha≤lam/(10*d) ∧ alpha≤θ/(200*(K:ℝ)^2) ∧
      0<γ ∧ γ≤eps ∧ γ≤eps/2 ∧ γ≤1/2 ∧ γ≤lam/(10*d) ∧ γ≤lam/10 ∧
      (∀(n A:ℕ), εtarget*n/2≤A→max alpha γ*n≤ρ*A ∧ 2*(max alpha γ*n)≤δ*A/4) ∧
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
    SuppliedVortexFixedSpacingOutcomeWithBalancedDegree r k₀ K d hr hK3 hm hd
      αRef sstar γRich tstar kstar θ ρ₀ (initialIndexDensity U Dnat) Dnat eps lam ζret alpha γ
      hθpos hθ hρ₀ hρlo hρhi hD hcut
      β βCommon εAbs εRob ζRob εRef δRef ζ εBal ζBal εNbr ζNbr εLoad ζLoad ζLocal ζConfig τLevel
      BM BO t₀ ξ Δ (τ₀/2) size a₀ b₀ e₀ aRob bRob eRob f₀ (Q.length-1) hNbr n (by omega)
      U F hF Allowed hAllowed hsize hclass P π weight w Dnat vsize βQ εQ Q hpres
end Oberwolfach
