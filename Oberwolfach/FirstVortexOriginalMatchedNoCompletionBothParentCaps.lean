module

public import Oberwolfach.FirstVortexOriginalMarginNoCompletionBothParentCaps
public import Oberwolfach.FirstVortexOriginalMarginAllReservesLateHostBothLevelTailsDensityCap
public import Oberwolfach.LongOriginalMatchedHostInputs
public import Oberwolfach.FirstVortexOriginalMarginAllReservesSeparateWeightsDensityCap
public import Oberwolfach.FirstVortexOriginalMarginSelectorHostGeometry
public import Oberwolfach.FirstVortexSharedAllReservesLevelSeparateWeights

@[expose] public section
/-! Start the all-reserve probability and uniform level construction from
the original host margin, with one shared choice of long-cycle parameters. -/
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

theorem first_vortex_original_matched_no_completion_both_parent_caps
    (α ρstar:ℝ) (hα:0<α) (hρstar:0<ρstar):
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
    let BA:=successorWeightUpper k₀ (αRef/4)
    ∃β βCommon εAbs εRob ζRob δAbs:ℝ,0<β ∧ 0<βCommon ∧ 0<εAbs ∧ 0<εRob ∧ 0<ζRob ∧ 0<δAbs ∧
    ∃εAbsP ζAbsP δAbsP βconfigP βCommonP:ℝ,
      0<εAbsP ∧ 0<ζAbsP ∧ 0<δAbsP ∧ 0<βconfigP ∧ 0<βCommonP ∧
    ∃εStable ζStable capStable:ℝ,0<εStable ∧ 0<ζStable ∧ 0<capStable ∧
      aLoA≤successorWeightLower k₀ ((2*αRef)/4) ∧ successorWeightUpper k₀ ((2*αRef)/4)≤BA ∧
      FirstVortexNamedAllReservesLateHostRetentionTailNoCompletion r (r+12) k₀ 1 αRef sstar ω γRich tstar kstar ρ₀ hρ
        β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable ∧
      FirstVortexUniformLevelActualParentTail r αRef ρ₀ href hρ βconfigP βCommonP
        (successorWeightLower k₀ ((2*αRef)/4)) (successorWeightUpper k₀ ((2*αRef)/4)) ∧
    ∃βfinal ρreserve:ℝ,0<βfinal ∧ βfinal≤1 ∧ βfinal≤βList/4 ∧ 0<ρreserve ∧
      βfinal+2*ρreserve≤βList/2 ∧
      (∀e:ℕ,∃N:ℕ,∀n:ℕ,N≤n→(e:ℝ)≤ρreserve*n) ∧
    ∃zetaCfg:ℝ,∃hzeta:0<zetaCfg,∃betaA:ℝ,0<betaA ∧ betaA≤βconfigP ∧ betaA≤βCommonP ∧
      3*betaA≤markedLocalCycleCoefficient r αRef (tstar/2) kstar-(r+5:ℕ)*zetaCfg ∧
      3*betaA≤markedLocalPathCoefficient r αRef (tstar/2) kstar-(r+4:ℕ)*zetaCfg ∧
    ∃Kgeom:ℕ,0<Kgeom ∧ ∃kappa0 ξ thetaDeep kappa:ℝ,0<kappa0 ∧ 0<ξ ∧ 0<thetaDeep ∧ 0<kappa ∧ kappa≤kappa0 ∧
    ∃ζCut hIcut εLevel deltaI:ℝ,0<ζCut ∧ ζCut≤1 ∧ ζCut≤tstar/16 ∧
      0<hIcut ∧ 2*hIcut≤αRef*kstar/4 ∧ 2*hIcut≤tstar/8-ζCut ∧
      0<εLevel ∧ εLevel≤hIcut ∧ 4*εLevel≤ξ ∧ εLevel≤kappa ∧ εLevel≤αRef/8 ∧ εLevel≤1/8 ∧
      0<deltaI ∧ deltaI<1/4 ∧ deltaI≤αRef/32 ∧ deltaI≤kstar/32 ∧ 2*deltaI≤tstar/8 ∧
    ∃cap:ℝ,0<cap ∧ cap≤capStable ∧ FirstVortexExactParentCapBound r αRef ρ₀ kappa zetaCfg thetaDeep BA cap href hρ ∧
      FirstVortexExactParentCapBound r αRef ρ₀ kappa zetaCfg thetaDeep (successorWeightUpper k₀ ((2*αRef)/4)) cap href hρ ∧
    ∃rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate:ℝ,
      FirstVortexAmbientGlobalData r ρ₀ cap (βfinal/2) rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate ∧
      δglobal≤(βfinal/200)^2 ∧
    ∃bmatch αMatch ε δold δlocal:ℝ,
      αMatch≤αRef ∧
      FirstVortexInitialMatchingVortexRates ρ₀ δglobal βList βfinal (min εLevel (min εStable ((2*αRef)/100000))) εInner εAbs εRob γRich kstar tstar (βList/32) bmatch αMatch ε ∧
      ε≤εStable ∧ ε≤(2*αRef)/100000 ∧
      0<δold ∧ δold≤1 ∧ δold≤δglobal ∧ δold<δlocal ∧ δlocal=2*δold ∧ δlocal≤δglobal ∧
      ∃(hm:7≤r+4) (htstarBound:tstar≤(1/100)/(((r+4):ℕ):ℝ)),
      FirstVortexLevelWithLateGeometryHighProbabilityNoCompletion r k₀ Kgeom αRef ρ₀ zetaCfg betaA ξ thetaDeep kappa ζCut hIcut deltaI aLoA BA ε ζRob href hρ hzeta
        cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate αMatch δold δlocal bmatch
        (r+12) 1 sstar ω γRich tstar kstar β βCommon εAbs εRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable hm htstarBound :=by
  obtain ⟨αRef,κL,ρ₀,href,hρ,hrefCap,hrefAlpha,hκ,hκcap,hρone,hρstarLe,hρκ,hmargin,hTail⟩:=
    first_vortex_original_margin_no_completion_both_parent_caps α ρstar hα hρstar
  refine ⟨αRef,κL,ρ₀,href,hρ,hrefCap,hrefAlpha,hκ,hκcap,hρone,hρstarLe,hρκ,hmargin,?_,hTail⟩
  intro n q D K hn θ hdegree hρlo hρhi P hreg F hF hthreshold hlong
  have hαcap:2*αRef≤α:=by linarith
  exact long_original_matched_host_inputs hn θ α αRef ρstar ρ₀ href hαcap hdegree hρstar hρ hρstarLe hρlo hρhi P hreg F hF hthreshold hlong
end Oberwolfach
