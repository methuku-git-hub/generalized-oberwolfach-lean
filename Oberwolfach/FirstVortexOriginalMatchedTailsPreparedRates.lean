module

public import Oberwolfach.FirstVortexOriginalMatchedBothLevelTails
public import Oberwolfach.FirstVortexOriginalPreparedRateContract

@[expose] public section
/-! Use one original choice of density and margin for the all-reserve event,
    both level tails, and the prepared matching and retention rates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxRecDepth 32768
set_option maxHeartbeats 120000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable
attribute [local instance 100000] Finset.decidableDforallFinset

theorem first_vortex_original_matched_both_tails_with_prepared_rates
    (α ρstar cap:ℝ) (hα:0<α) (hρstar:0<ρstar) (hcap:0<cap):
    ∃ (αRef κL ρ₀:ℝ) (href:0<αRef) (hρ:0<ρ₀),2*αRef≤1 ∧ 2*αRef≤α/2 ∧
      0<κL ∧ κL≤α/1000 ∧ ρ₀≤1 ∧ ρ₀≤ρstar ∧ ρ₀≤2*κL ∧
      (∀δ D:ℝ,∀n:ℕ,(δ+α/2)*(n:ℝ)≤D→(δ+2*αRef)*(n:ℝ)≤D) ∧
      (∀(n q D K:ℕ),0<n→∀θ:ℝ,(θ+α)*(n:ℝ)≤D→
        ρstar≤2*(q:ℝ)/(D:ℝ)→2*(q:ℝ)/(D:ℝ)≤1→
        ∀(P:SimpleGraph (Fin n)),P.IsRegularOfDegree D→
        ∀(F:Fin q→SimpleGraph (Fin n)),(∀w,(F w).IsRegularOfDegree 2)→
        (∀w v,cycleThreshold (Fintype.card ((F w).connectedComponentMk v))≤θ)→
        (∀w,(n:ℝ)/2≤((Finset.univ.filter (fun v=>K<Fintype.card ((F w).connectedComponentMk v))).card:ℝ))→
        ∃Allowed:Set ℕ,Allowed.Nonempty ∧ (∀s∈Allowed,3≤s) ∧ allowedThreshold Allowed≤θ ∧
          (allowedThreshold Allowed+2*αRef)*(n:ℝ)≤D ∧ (∀w,AllowedCycleLengths (F w) Allowed) ∧
          (∀w,factorPreparationClass (F w) K=none) ∧
          0<q ∧ 0<D ∧ (n:ℝ)/2≤D ∧ (D:ℝ)≤2*n ∧ (1/2+2*αRef)*n≤(D:ℝ) ∧
          ρ₀≤ initialIndexDensity (Fin q) D ∧ initialIndexDensity (Fin q) D≤1 ∧
          initialIndexDensity (Fin q) D*(D:ℝ)=2*Fintype.card (Fin q) ∧ Fintype.card (Fin q)≤n) ∧
    ∀L₀:ℕ,
    let βList:ℝ:=(min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16;
    ∃m r k₀:ℕ,7≤m ∧ L₀≤m ∧ Even (m+1) ∧ 2≤r ∧ r+4=m ∧
      r+4+1=(k₀+2)*2 ∧ successorCycleRatio k₀+αRef/2≤1/2+αRef ∧
      1/(100*((r+4:ℕ):ℝ))≤βList/16 ∧
    ∃A BM:ℝ,0<A ∧ 0<BM ∧
      (∀K d:ℕ,0<K→2≤d→
        ∃BO:Fin K→ℝ,(∀i,0<BO i) ∧ HostMatchingVortexContinuation m K d (2*αRef) A BM BO) ∧
    let sstar:ℝ:=1/100
    let tstar:ℝ:=1/(200*((r+4:ℕ):ℝ))
    let kstar:ℝ:=ρ₀/(800*((r+4:ℕ):ℝ))
    let ω:ℝ:=ρ₀/4
    let γRich:ℝ:=min αRef (1/2:ℝ)/2
    let aLoA:=successorWeightLower k₀ (αRef/4)
    let BA:=successorWeightUpper k₀ (αRef/4);
    ∃β βCommon εAbs εRob ζRob δAbs:ℝ,0<β ∧ 0<βCommon ∧ 0<εAbs ∧ 0<εRob ∧ 0<ζRob ∧ 0<δAbs ∧
    ∃εAbsP ζAbsP δAbsP βconfigP βCommonP:ℝ,
      0<εAbsP ∧ 0<ζAbsP ∧ 0<δAbsP ∧ 0<βconfigP ∧ 0<βCommonP ∧
    ∃εStable ζStable capStable:ℝ,0<εStable ∧ 0<ζStable ∧ 0<capStable ∧
      aLoA≤successorWeightLower k₀ ((2*αRef)/4) ∧ successorWeightUpper k₀ ((2*αRef)/4)≤BA ∧
      FirstVortexNamedAllReservesProbabilityTail r (r+12) k₀ 1 αRef sstar ω γRich tstar kstar ρ₀ hρ
        β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable ∧
      FirstVortexUniformLevelActualParentTailExactMargin r αRef ρ₀ href hρ βconfigP βCommonP aLoA BA ∧
      FirstVortexUniformLevelActualParentTail r αRef ρ₀ href hρ βconfigP βCommonP
        (successorWeightLower k₀ ((2*αRef)/4)) (successorWeightUpper k₀ ((2*αRef)/4)) ∧
      FirstVortexInitialVortexReserveData αRef ρ₀ ∧ FirstVortexOriginalPreparedRateContract r ρ₀ cap αRef :=by
  obtain ⟨αRef,κL,ρ₀,href,hρ,hrefCap,hrefAlpha,hκ,hκcap,hρone,hρstarLe,hρκ,hmargin,hHost,hTail⟩:=
    first_vortex_original_matched_all_reserves_both_level_tails α ρstar hα hρstar
  refine ⟨αRef,κL,ρ₀,href,hρ,hrefCap,hrefAlpha,hκ,hκcap,hρone,hρstarLe,hρκ,hmargin,hHost,?_⟩
  intro L₀ βList
  obtain ⟨m,r,k₀,hm,hL,heven,hr,hrEq,hlen,hgap,htrim,A,BM,hA,hBM,hweights,
    β,βCommon,εAbs,εRob,ζRob,δAbs,hβ,hβCommon,hεAbs,hεRob,hζRob,hδAbs,
    εAbsP,ζAbsP,δAbsP,βconfigP,βCommonP,hεAbsP,hζAbsP,hδAbsP,hβconfigP,hβCommonP,
    εStable,ζStable,capStable,hεStable,hζStable,hcapStable,haLo,hBA,hprob,hExact,hParent,hInitial⟩:=hTail L₀
  refine ⟨m,r,k₀,hm,hL,heven,hr,hrEq,hlen,hgap,htrim,A,BM,hA,hBM,hweights,
    β,βCommon,εAbs,εRob,ζRob,δAbs,hβ,hβCommon,hεAbs,hεRob,hζRob,hδAbs,
    εAbsP,ζAbsP,δAbsP,βconfigP,βCommonP,hεAbsP,hζAbsP,hδAbsP,hβconfigP,hβCommonP,
    εStable,ζStable,capStable,hεStable,hζStable,hcapStable,haLo,hBA,hprob,hExact,hParent,hInitial,?_⟩
  exact first_vortex_original_prepared_rate_contract r ρ₀ cap αRef hρ hρone hcap href (by omega)
end Oberwolfach
