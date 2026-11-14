module

public import Oberwolfach.FirstVortexClassPrepareEarlyMatchingSingleLevel
public import Oberwolfach.FirstVortexClassPrepareEarlyMatching
public import Oberwolfach.LongEarlyMatchingUniformResidualInput
public import Oberwolfach.LongCapacityAutomaticMargins
public import Oberwolfach.LongFirstPrescribedAsymptotic
public import Oberwolfach.FirstVortexClassPreparedOrientedOutcome
public import Oberwolfach.FirstVortexClassSourceFromRetainedTests
public import Oberwolfach.FirstVortexPreparedOrientedOutcome
public import Oberwolfach.FirstVortexOrientedAutomaticCoefficients
public import Oberwolfach.FirstVortexPreparedOrientedOutcome
public import Oberwolfach.FirstVortexProtectedAutomaticCoefficients
public import Oberwolfach.FirstVortexPreparedOrientedOutcome

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 80000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexClassSixTestsMatchingFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_class_prepare_from_six_tests_and_early_matching
    (α lam lamAssign ε δold δlocal θ eps ξ ρ₀ bmatch ξPart:ℝ) (d K r:ℕ)
    (hα:0<α) (hlam:0<lam) (hε:0<ε) (hδ:0<δold) (hθ:0<θ)
    (hρ₀:0<ρ₀) (hbmatch:0<bmatch) (hαb:(2*α)/16≤bmatch)
    (hbd:bmatch≤((ρ₀/4)/40000)/16) (hεsmall:ε≤(ρ₀/4)/80000)
    (hθδ:10*θ≤δold) (hθlocal:θ≤δold/32) (hθhi:θ≤1/100)
    (hlamlocal:lam≤δold*ε/32) (hspacing:1/(d:ℝ)≤θ/1024)
    (hd:3≤d) (hK:3≤K) (hm:7≤(r+4))
    (heps:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hξ:4*ξ≤eps/2) (hξ0:0≤ξ):
    ∃N:ℕ,∀n:ℕ,N≤n→∀ [Nonempty (Fin n)] (U:Type) [Fintype U] [DecidableEq U]
    (P Sclass:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (Dv mm:ℕ) (β:ℝ) (Vort:Vortex U P Dv β ε mm)
    (hreg:P.IsRegularOfDegree Dv) (hDv:0<Dv) (hρhi:initialIndexDensity U Dv≤1)
    (hρlo:ρ₀ ≤ initialIndexDensity U Dv) (hDlo:(n:ℝ)/2≤Dv) (hDhi:(Dv:ℝ)≤2*n) (hmm:0<mm)
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hclass:∀u,factorPreparationClass (F u) K=none)
    (hcut:(1/(((r+4):ℝ)+1))/(d:ℝ)≤θ)
    (hcutHost:5/((((r+4):ℝ)+1)*(d:ℝ)+5)+(((r+4):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (C₀:ℝ) (hC:1≤C₀) (hehi:ε≤α/(1000*C₀)) (hlamhi:lam≤α/128) (hlamθ:lam≤θ)
    (a γ ζ ρ Δ:ℝ) (hγ:0≤γ) (ha0:0≤a) (hγε:γ≤eps) (heps1:eps≤1)
    (ha:a≤lam/(10*d)) (hγrate:γ≤lam/(10*d))
    (hζ:ζ≤θ/4096) (hρ:ρ≤θ/4096) (hζ0:0≤ζ)
    (hscale:max a γ*n≤ρ*(Vort.extendedVertices 1).card)
    (τ Asrc BM:ℝ) (hBM:0<BM) (weight:(Fin ((r+4)+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) Dv τ Asrc BM weight)
    (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ) (hw0:∀i C,0≤w i C)
    (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i))
    (z:MarkedExpandedActualOutcome (U:=U) π d) (Inner:Finset (Fin n)) (βList:ℝ)
    (terr τerr:ℝ) (hτerr:0≤τerr)
    (hSP:Sclass≤P)
    (hedit:∀v,((changed ((longPhysicalStateGraph P (z.1) {0,1,2,3,4}).neighborFinset v) (Sclass.neighborFinset v)).card:ℝ)≤ξPart*n)
    (hξdeg:ξPart≤(2*α)/32) (hξedges:ξPart/2≤(lamAssign-lam)*ε)
    (hmargin:ξPart*n≤(δlocal-δold)*((Vort.extendedVertices 1).card:ℝ)),
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e ((z.1) e)
    let σ:=fun e=>raw (Sum.inr e)
    let ni:=@longPaddedSeedExponent K
    let hni:=@long_padded_seed_exponent_positive K
    let ℓ:=fun i=>ni i+2
    let p:=(∑u,longAssignedApproxOrdinaryWeight F hF K (r+4) θ u)/(Dv:ℝ)
    let k:=(∑u,longAssignedApproxMarkedWeight F hF K (r+4) θ u)/(Dv:ℝ)
    let udens:=2*(∑u,(1-(1/100:ℝ)-(1/100:ℝ)/((r+4):ℝ)-longAssignedApproxMarkedWeight F hF K (r+4) θ u-longAssignedApproxOrdinaryWeight F hF K (r+4) θ u))/(Dv:ℝ)
    let pstar:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*(((r+4):ℝ)+1))))
    let BMseed:=2*BM/pstar^(2*(r+4)+1)
    let BOseed:=fun i=>2*BO i/pstar^(2*(ni i+2))
    let C:=10*((((r+4):ℝ)+1)^4*BMseed+∑i:Fin K,((ni i:ℝ)+2)^4*BOseed i)
    let Wm:=longAssignedMarkedSeed F hF K (r+4) d θ Dv π weight
    let Wo:=longAssignedOrdinarySeed F hF K (r+4) d θ Dv P π ni hni w
    let W:=longMixedSeedWeight Wm Wo
    let Rsrc:=longRawHubResources (U:=U) π d (r+4) ℓ
    let R:=mixedCandidateResources Rsrc
    let state:=longRawHubState P π d raw true true
    let hub:=longRawHubNames (U:=U) π d (r+4) ℓ
    ((∀v,|(((P.neighborFinset v∩Vort.extendedVertices 1).filter (fun x=>((z.1) (Sum.inl s(v,x))).1=4)).card:ℝ)-
      udens*(P.neighborFinset v∩Vort.extendedVertices 1).card|<(n:ℝ)^(3/4:ℝ)) ∧
    (∀u,
      |rawIntervalUnassignedHubCountOn π d σ u (Vort.extendedVertices 1)-
      ((Vort.extendedVertices 1).card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K (r+4) θ u g)-
        (∑k,longAssignedSpokeProbability F hF K (r+4) θ u k))|<((Vort.extendedVertices 1).card:ℝ)^(3/4:ℝ)) ∧
    (∀v,
      |rawIntervalUnassignedColumnCount π d σ v (Vort.extendedIndices 1)-
      ∑u∈Vort.extendedIndices 1,(1-(∑g,longAssignedIntervalProbability F hF K (r+4) θ u g)-
        (∑k,longAssignedSpokeProbability F hF K (r+4) θ u k))|<((Vort.extendedVertices 1).card:ℝ)^(3/4:ℝ)) ∧
    (∀v∈Vort.extendedVertices 1,
      ((rawIntervalBoundaryHubSet π d σ (Vort.extendedIndices 1) v).card:ℝ)≤
        4*((Vort.extendedIndices 1).card:ℝ)/d+4*((Vort.extendedVertices 1).card:ℝ)^(3/4:ℝ)) ∧
    (RetainedRestrictionLocalGood π d σ false (startRetentionMinimum (rawStartHubSet π d (fun e=>rawExpandedMarkedCollapse (Sum.inr e) (z.1 (Sum.inr e))) false))
      (Vort.extendedVertices 1) (Vort.extendedIndices 1) ζ (z.2)) ∧
    (∀x y,x≠y→(5/8:ℝ)*(1/100:ℝ)^2*Fintype.card U-(n:ℝ)^(3/4:ℝ)≤
      (((Finset.univ:Finset U).filter (fun u=>rawIntervalFamilyState π d σ (x,u)=some (Sum.inr false) ∧
        rawIntervalFamilyState π d σ (y,u)=some (Sum.inr false))).card:ℝ)))→
    (∀v,((rawIntervalExtendedAnyHubSet π d σ v).card:ℝ)≤4*(Fintype.card U:ℝ)/((r+4):ℝ)+4*(n:ℝ)^(3/4:ℝ))→
    (∀u g,|rawIntervalHubStartCount π d g σ u-(n:ℝ)*longAssignedIntervalProbability F hF K (r+4) θ u g/d|<(n:ℝ)^(3/4:ℝ)/d)→
    (∀u,|(((ordinaryCommonHubSpokeRoots u).filter (fun v=>state v=true)).card:ℝ)-
      longAssignedApproxOrdinaryWeight F hF K (r+4) θ u*n|≤ξ*n)→
    (∀(i:Option (Fin K)) (root:LongRawHubResource n U),state root=true→
      |resourcePatternLoad (Rsrc i) (W i) (fun _ _=>true) root state-
        longAssignedMixedTarget F hF K (r+4) θ Dv p k i root|≤terr+τerr*longAssignedMixedTarget F hF K (r+4) θ Dv p k i root)→
    (∀(Del:SimpleGraph (Fin n)) (δDel:ℝ), (∀x,(Del.degree x:ℝ)≤δDel)→δDel≤Δ*n→
      0≤terr+C*(δDel/(n:ℝ))+4*τerr ∧ terr+C*(δDel/(n:ℝ))+4*τerr≤eps/2)→
    (∀Del:SimpleGraph (Fin n),(∀v,(Del.degree v:ℝ)≤Δ*n)→
      LongEarlyMatchingListsForDeletion r K d θ Dv a γ eps Δ βList P π F hF weight w z Inner Del)→
    FirstVortexClassPreparedOrientedOutcome P Sclass π Dv mm d (r+4) β ε Vort F hF θ lamAssign eps δlocal α bmatch ρ₀ ξ Δ a γ weight w (z.1) (startRetentionMinimum (rawStartHubSet π d (fun e=>rawExpandedMarkedCollapse (Sum.inr e) (z.1 (Sum.inr e))) false)) (z.2) :=by
  obtain ⟨N,hN⟩:=first_vortex_class_oriented_source_from_retained_tests α lam ε δold θ eps ξ d K (r+4) hα hlam hε hδ hθ hθδ hθlocal hθhi hlamlocal hspacing hd (by omega) (by omega) heps hξ
  obtain ⟨Nlarge,hLarge⟩:=long_capacity_large_order (r+4) θ hθ
  obtain ⟨Nerror,hError⟩:=long_first_prescribed_matching_asymptotic bmatch (ρ₀/4) hbmatch (by positivity)
  refine ⟨max (max (max N Nlarge) Nerror) 1,?_⟩
  intro n hn _ U _ _ P Sclass π Dv mm β Vort hreg hDv hρhi hρlo hDlo hDhi hmm F hF Allowed hAllowed hclass hcut hcutHost hnoshort C₀ hC hehi hlamhi hlamθ a γ ζ ρ Δ hγ ha0 hγε heps1 ha hγrate hζ hρ hζ0 hscale τ Asrc BM hBM weight hw BO hBO w hw0 hwupper z Inner βList terr τerr hτerr hSP hedit hξdeg hξedges hmargin raw σ ni hni ℓ p k udens pstar BMseed BOseed C Wm Wo W Rsrc R state hub hSix hboundaryGlobal hstarts hcount hload hbudget hEarly
  obtain ⟨hrow,hfixedAll,hcolumnAll,hboundary,hrows,hpair⟩:=hSix
  have hfixed:=fun u (_:u∈Vort.extendedIndices 1)=>hfixedAll u
  have hcolumn:=fun v (_:v∈Vort.extendedVertices 1)=>hcolumnAll v
  have hmatching:=long_early_matching_uniform_residual_input r K d θ Dv a γ eps Δ βList P π F hF weight w z Inner hEarly
  have hn0:0<n:=by omega
  have hcutSource:=long_capacity_cutoff_succ (r+4) d K (by omega) θ (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hcutHost)
  have hlarge:=hLarge n (by omega)
  have herror:=(hError n (by omega)).2
  have hDvR:0<(Dv:ℝ):=by exact_mod_cast hDv
  have hsize:initialIndexDensity U Dv*(Dv:ℝ)=2*Fintype.card U:=by
    dsimp [initialIndexDensity]; field_simp
  have hcoeff:=long_assigned_actual_matching_coefficients hn0 F hF Allowed hAllowed K (by omega) (r+4) d (by omega) (by omega) θ ρ₀ (initialIndexDensity U Dv) Dv hθ.le hθhi hρ₀ hρlo hρhi hDvR hsize (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hcut) hclass
  have hb:∀u,(1/4:ℝ)≤longAssignedApproxOrdinaryWeight F hF K (r+4) θ u:=fun u=>(hcoeff.1 u).1
  have hN':=hN n (by omega)
  have hdec:firstClassSourceFromRetainedTestsFin n=firstVortexClassSixTestsMatchingFin n:=Subsingleton.elim _ _
  have hdec6:firstClassSourceFromRetainedTestsFin 6=firstVortexClassSixTestsMatchingFin 6:=Subsingleton.elim _ _
  try rw [hdec] at hN'
  try rw [hdec6] at hN'
  unfold FirstVortexClassPreparedOrientedOutcome
  have hdecP:firstVortexClassPreparedOutcomeFin n=firstVortexClassSixTestsMatchingFin n:=Subsingleton.elim _ _
  have hdecPK:firstVortexClassPreparedOutcomeFin K=firstVortexClassSixTestsMatchingFin K:=Subsingleton.elim _ _
  try rw [hdecP]
  try rw [hdecPK]
  intro ni' hni' ℓ' raw' selected Hret Wm' Wo' W' Rsrc' R' hub' Del δDel hDel hΔ hξDel S T e Q q
  obtain ⟨M,hpos,hdisj,hinc,hlow,hup,hsourceCount⟩:=hmatching Del δDel hDel hΔ
  refine ⟨M,hpos,hdisj,hinc,hlow,hup,hsourceCount,?_⟩
  intro D absorber Reserve X Z habs H' A' Used P₀ Sel Kbad
  obtain ⟨herr0,herrle⟩:=hbudget Del δDel hDel hΔ
  exact hN' U P π Dv mm β Vort hreg hDv hρhi ρ₀ hρ₀ hρlo hDlo hmm (z.1) Del D (startRetentionMinimum (rawStartHubSet π d (fun e=>rawExpandedMarkedCollapse (Sum.inr e) (z.1 (Sum.inr e))) false)) (z.2) M F hF C₀ a γ δDel hC hehi hlamhi hγ ha0 ha hγrate hDel hξDel (fun v _=>by simpa only [udens,Nat.cast_add,Nat.cast_ofNat] using hrow v) hinc hboundary absorber ζ ρ hζ hρ hζ0 hscale hrows hfixed hcolumn Allowed hAllowed hK (by omega) (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hcut) hclass hnoshort hcutSource hlarge τ Asrc BM hBM weight hw hDhi BO hBO w hw0 hwupper hstarts Reserve X Z p k τerr terr (ξ*n) hlamθ (by linarith) hb hτerr (by positivity) (first_vortex_common_event_count_budget n ξ eps hξ) hγε (le_trans hγ hγε) heps1 hload hcount (by simpa only [C,pstar,BMseed,BOseed,Nat.cast_add,Nat.cast_ofNat] using herr0) (by simpa only [C,pstar,BMseed,BOseed,Nat.cast_add,Nat.cast_ofNat] using herrle) habs hpos hdisj hlow hup Sclass ξPart bmatch lamAssign δlocal hSP hedit hbmatch.le hbd hαb hξdeg hξedges hεsmall herror hpair hmargin
end Oberwolfach
