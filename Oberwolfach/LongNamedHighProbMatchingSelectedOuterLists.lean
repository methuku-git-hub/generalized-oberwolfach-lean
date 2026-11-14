module

public import Oberwolfach.LongNamedHighProbMatchingSelectedLists
public import Oberwolfach.MarkedSelectedMatchingOuterListScales

@[expose] public section
/-! Carry the outer reserved-list bounds with the exact named selected scales. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 120000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable
attribute [local instance 100000] Finset.decidableDforallFinset
def LongNamedHighProbMatchingSelectedOuterListsForWeights
    (r h k₀ Qpow:ℕ) (hr:2≤r) (hQpow:0<Qpow) (hlen:r+4+1=(k₀+2)*2)
    (αRef sstar ω γRich tstar kstar:ℝ)
    (hαRef:0<αRef) (hsstar:0<sstar) (hsstar1:sstar≤1/100) (hω:0<ω)
    (hmargin:successorCycleRatio k₀+αRef/2≤1/2+αRef)
    (hγRich:0<γRich) (hγRich1:γRich≤1/2) (hγcap:γRich≤αRef)
    (htstar:0<tstar) (htstar1:tstar≤1) (horder:tstar≤sstar) (hkstar:0<kstar)
    (K:ℕ) (hK3:3≤K) (hm:7≤(r+4))
    (θ ρ₀:ℝ) (hθpos:0<θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hωBound:4*ω≤ρ₀)
    (ε₀ lam ηEvent:ℝ) (hηEvent:0<ηEvent) (hε₀:ε₀<1) (hlam:0<lam) (hlamθ:lam≤θ)
    (htstarBound:tstar≤(1/100)/(((r+4):ℕ):ℝ))
    (d:ℕ) (hd:2≤d) (hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ)
    (gamma pA0 αGeom omega0 t0 p0 aLoA BA:ℝ)
    (BM:ℝ) (hBM:0<BM) (BO:Fin K→ℝ) (hBO:∀i,0<BO i) (εcap βE:ℝ) (m:ℕ):Prop :=
    ∃ εExtra:ℝ,0<εExtra ∧ (0<ε₀→4*εExtra≤ε₀) ∧ ∃eps:ℝ,0<eps ∧ eps≤1 ∧ 3*eps≤lam*(θ/(100*(K:ℝ)^2)) ∧
    let alpha:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let γ:=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)))
    0<alpha ∧ alpha≤θ/(200*(K:ℝ)^2) ∧ 0<γ ∧ γ≤eps ∧
    let ni:=@longPaddedSeedExponent K
    let hni:=@long_padded_seed_exponent_positive K
    let hpadded:=@long_padded_seed_length_eq_exponent K
    let pstar₀:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*((((r+4):ℕ):ℝ)+1))))
    let BMseed₀:=2*BM/pstar₀^(2*(r+4)+1)
    let BOseed₀:=fun i=>2*BO i/pstar₀^(2*(ni i+2))
    let Kpair₀:=1+((((r+4):ℕ):ℝ)+1)^4*BMseed₀+∑i:Fin K,((ni i:ℝ)+2)^3*BOseed₀ i
    let C₀:=10*(((((r+4):ℕ):ℝ)+1)^4*BMseed₀+∑i:Fin K,((ni i:ℝ)+2)^4*BOseed₀ i)
    ∃ β βCommon εAbs εRob ζRob δAbs:ℝ,0<β∧0<βCommon∧0<εAbs∧0<εRob∧0<ζRob∧0<δAbs ∧
    ∃ εAbsP ζAbsP δAbsP βconfigP βCommonP:ℝ,
      0<εAbsP ∧ 0<ζAbsP ∧ 0<δAbsP ∧ 0<βconfigP ∧ 0<βCommonP ∧
      MarkedSelectedLevelMatchingOuterListScalesResult r ρ₀ omega0 t0 p0 βconfigP βCommonP aLoA BA gamma pA0 αGeom
        (fun gammaLoss sigmaLoss κmax => LongNamedMatchingHighProbListsAfterLosses r h k₀ Qpow hr hQpow hlen αRef sstar ω γRich tstar kstar hαRef hsstar hsstar1 hω hmargin hγRich hγRich1 hγcap htstar htstar1 horder hkstar K hK3 hm θ ρ₀ hθpos hθ hρ₀ hωBound ε₀ lam ηEvent hηEvent hε₀ hlam hlamθ htstarBound d hd hcut gamma pA0 αGeom omega0 t0 p0 aLoA BA BM hBM BO hBO εExtra eps β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP gammaLoss sigmaLoss κmax) εAbs εRob γRich kstar tstar ζRob εcap αRef βE m

theorem long_named_high_prob_matching_selected_outer_lists_for_weights
    (r h k₀ Qpow:ℕ) (hr:2≤r) (hQpow:0<Qpow) (hlen:r+4+1=(k₀+2)*2)
    (αRef sstar ω γRich tstar kstar:ℝ)
    (hαRef:0<αRef) (hsstar:0<sstar) (hsstar1:sstar≤1/100) (hω:0<ω)
    (hmargin:successorCycleRatio k₀+αRef/2≤1/2+αRef)
    (hγRich:0<γRich) (hγRich1:γRich≤1/2) (hγcap:γRich≤αRef)
    (htstar:0<tstar) (htstar1:tstar≤1) (horder:tstar≤sstar) (hkstar:0<kstar)
    (K:ℕ) (hK3:3≤K) (hm:7≤(r+4))
    (θ ρ₀:ℝ) (hθpos:0<θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hωBound:4*ω≤ρ₀)
    (ε₀ lam ηEvent:ℝ) (hηEvent:0<ηEvent) (hε₀:ε₀<1) (hlam:0<lam) (hlamθ:lam≤θ)
    (htstarBound:tstar≤(1/100)/(((r+4):ℕ):ℝ))
    (d:ℕ) (hd:2≤d) (hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ)
    (gamma pA0 αGeom omega0 t0 p0 aLoA BA:ℝ)
    (BM:ℝ) (hBM:0<BM) (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (αHost βRaw βE:ℝ) (m:ℕ) (hα:αRef=αHost/2)
    (hβ:βRaw=(min αHost (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16)
    (hE:βE=βRaw/2) (htrim:1/(100*(m:ℝ))≤βE/8)
    (hInput:LongNamedHighProbMatchingSelectedListsForWeights r h k₀ Qpow hr hQpow hlen αRef sstar ω γRich tstar kstar hαRef hsstar hsstar1 hω hmargin hγRich hγRich1 hγcap htstar htstar1 horder hkstar K hK3 hm θ ρ₀ hθpos hθ hρ₀ hωBound ε₀ lam ηEvent hηEvent hε₀ hlam hlamθ htstarBound d hd hcut gamma pA0 αGeom omega0 t0 p0 aLoA BA BM hBM BO hBO (βRaw/32)):
    LongNamedHighProbMatchingSelectedOuterListsForWeights r h k₀ Qpow hr hQpow hlen αRef sstar ω γRich tstar kstar hαRef hsstar hsstar1 hω hmargin hγRich hγRich1 hγcap htstar htstar1 horder hkstar K hK3 hm θ ρ₀ hθpos hθ hρ₀ hωBound ε₀ lam ηEvent hηEvent hε₀ hlam hlamθ htstarBound d hd hcut gamma pA0 αGeom omega0 t0 p0 aLoA BA BM hBM BO hBO (βRaw/32) βE m := by
  obtain ⟨εExtra,hεExtra,hεExtraSmall,eps,heps,heps1,hepsBudget,hAlpha0,hAlphaBound,hγ,hγeps,
    β,βCommon,εAbs,εRob,ζRob,δAbs,hβ0,hβCommon,hεAbs,hεRob,hζRob,hδAbs,
    εAbsP,ζAbsP,δAbsP,βconfigP,βCommonP,hεAbsP,hζAbsP,hδAbsP,hβconfigP,hβCommonP,hSelected⟩:=hInput
  refine ⟨εExtra,hεExtra,hεExtraSmall,eps,heps,heps1,hepsBudget,hAlpha0,hAlphaBound,hγ,hγeps,
    β,βCommon,εAbs,εRob,ζRob,δAbs,hβ0,hβCommon,hεAbs,hεRob,hζRob,hδAbs,
    εAbsP,ζAbsP,δAbsP,βconfigP,βCommonP,hεAbsP,hζAbsP,hδAbsP,hβconfigP,hβCommonP,?_⟩
  exact marked_selected_matching_outer_list_scales r ρ₀ omega0 t0 p0 βconfigP βCommonP aLoA BA gamma pA0 αGeom _
    εAbs εRob γRich kstar tstar ζRob αHost αRef βRaw βE m hα hβ hE htrim hSelected
end Oberwolfach
