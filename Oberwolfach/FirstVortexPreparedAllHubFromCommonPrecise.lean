module

public import Oberwolfach.FirstVortexPreparedPreciseCommonToGlobal
public import Oberwolfach.FirstVortexPreparedGlobalToAllHubPrecise
public import Oberwolfach.FirstVortexRetainedAllHubLoadFromPreciseDegree
public import Oberwolfach.FirstVortexClassPreparedRetainedFullPackingAllHub
public import Oberwolfach.FirstVortexCapacityInputsFromCommonMatching
public import Oberwolfach.FirstVortexRetainedDynamicGlobalLoadFromBoundary
public import Oberwolfach.FirstVortexRetainedDynamicResidualUpper
public import Oberwolfach.LongSelectedRetainedSourceDynamicBad
public import Oberwolfach.LongSelectedRetainedSourceDynamicCapacity
public import Oberwolfach.LongSelectedRetainedSourceDynamicGlobalLoad
public import Oberwolfach.FirstVortexClassPreparedRetainedFullPackingCapacity
public import Oberwolfach.FirstVortexClassPreparedRetainedFullPackingGlobal
public import Oberwolfach.FirstVortexDynamicGlobalLoadFromBoundary
public import Oberwolfach.FirstVortexDynamicResidualUpper
public import Oberwolfach.FirstVortexClassPreparedOrientedCapacity
public import Oberwolfach.FirstVortexClassPreparedOrientedGlobal
public import Oberwolfach.FirstVortexOrientedGlobalLoadFromBoundary
public import Oberwolfach.FirstVortexPreparedOrientedCapacity
public import Oberwolfach.FirstVortexPreparedOrientedGlobal
public import Oberwolfach.FirstVortexOrientedResidualUpper
public import Oberwolfach.FirstVortexOrientedGlobalLoad
public import Oberwolfach.FirstVortexPreparedOutcomeGlobalLoad

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexPreparedAllHubAssembledFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_class_prepared_all_hub_from_common_precise
    (ε θ δglobal ρ₀ lam lamAssign ζret α ξEdit:ℝ) (m d:ℕ) (hm:0<m) (hdlarge:m+2≤d)
    (hε:0<ε) (hθ:0<θ) (hθ1:θ≤1) (hδglobal:0<δglobal) (hθδ:10*θ≤δglobal)
    (hmarg:4/(m:ℝ)≤δglobal/4)
    (Nret:ℕ) (hNret:∀n:ℕ,Nret≤n→∀q errOrd:ℝ,
      q≤1/((m:ℝ)+1)→errOrd≤θ*n→
      (n:ℝ)*q/d+(((m+1)*d-1:ℕ):ℝ)*(2*((n:ℝ)^(3/4:ℝ)/d)+ζret*n)+errOrd≤4*θ*n)
    (hρhi:ρ₀≤1) (hεsmall:ε≤(ρ₀/4)/80000)
    (hlam:0≤lam) (hlampos:0<lam) (hlam1:lam≤1) (hd:0<d) (hspacing:1/(d:ℝ)≤θ/1024)
    (hα:0<α) (hρ₀:0<ρ₀) (hθmax:θ≤1/100)
    (hsmall:lam+ξEdit≤((ρ₀/4)/40000)*θ/4096)
    (hεprecise:ε≤((ρ₀/4)/40000)/8192) (hlamθ:lam≤θ):
    ∃N:ℕ,∀n K:ℕ,N≤n→3≤K→∀(U:Type) [Fintype U] [DecidableEq U]
    (P Sclass:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (Dv mm:ℕ) (β:ℝ) (Vort:Vortex U P Dv β ε mm)
    (hreg:P.IsRegularOfDegree Dv) (hDv:0<Dv) (hρ:initialIndexDensity U Dv≤1) (hmm:0<mm)
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (δlocal bmatch eps ξ Δ a γ ρscale:ℝ)
    (heps0:0≤eps)
    (hepsAssign:3*eps≤lam*(θ/(100*(K:ℝ)^2)))
    (C₀ u:ℝ) (hC:1≤C₀) (hεα:ε≤α/(1000*C₀)) (hlamα:lam≤α/128)
    (hu0:0≤u) (hu:u≤2*θ) (hUle:Fintype.card U≤n) (hmax:2*max a (4*γ)≤lam/3)
    (hΔlam:Δ≤lam/3) (hSP:Sclass≤P)
    (hγ:0≤γ) (ha:a≤lam/(10*d)) (hγcap:γ≤lam/(10*d))
    (hζ:ζret≤θ/4096) (hζ0:0≤ζret) (hρscale:ρscale≤θ/4096) (hρscale0:0≤ρscale)
    (hscale:max a γ*n≤ρscale*(Vort.extendedVertices 1).card)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (weight:(Fin (m+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (σE:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (hedit:∀v,((changed ((longPhysicalStateGraph P σE {0,1,2,3,4}).neighborFinset v) (Sclass.neighborFinset v)).card:ℝ)≤ξEdit*n)
    (hrows4:∀v∈Vort.extendedVertices 1,|(((P.neighborFinset v∩Vort.extendedVertices 1).filter (fun w=>(σE (Sum.inl s(v,w))).1=4)).card:ℝ)-
      u*(P.neighborFinset v∩Vort.extendedVertices 1).card|<(n:ℝ)^(3/4:ℝ))
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) false) t),
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σE e)
    let σ:=fun e=>raw (Sum.inr e)
    let H:=Vort.extendedIndices 1
    let A:=Vort.extendedVertices 1
    (RetainedRestrictionLocalGood π d σ false t A H ζret Jret)→
    (∀u∈H,|rawIntervalUnassignedHubCountOn π d σ u A-
      (A.card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K m θ u g)-
        (∑j,longAssignedSpokeProbability F hF K m θ u j))|<(A.card:ℝ)^(3/4:ℝ))→
    (∀v∈A,|rawIntervalUnassignedColumnCount π d σ v H-
      ∑u∈H,(1-(∑g,longAssignedIntervalProbability F hF K m θ u g)-
        (∑j,longAssignedSpokeProbability F hF K m θ u j))|<(A.card:ℝ)^(3/4:ℝ))→
    (∀v,((rawIntervalBoundaryHubSet π d σ Finset.univ v).card:ℝ)≤
      4*(Fintype.card U:ℝ)/d+4*(n:ℝ)^(3/4:ℝ))→
    (∀u g,|rawIntervalHubStartCount π d g σ u-(n:ℝ)*longAssignedIntervalProbability F hF K m θ u g/d|<(n:ℝ)^(3/4:ℝ)/d)→
    (RetainedRestrictionGood π d σ false t (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζret Jret)→
    (∀v,((rawIntervalExtendedAnyHubSet π d σ v).card:ℝ)≤4*(Fintype.card U:ℝ)/(m:ℝ)+4*(n:ℝ)^(3/4:ℝ))→
    (∀w,|rawIntervalUnassignedHubCountOn π d σ w A-
      (A.card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j))|<(n:ℝ)^(3/4:ℝ))→
    (∀v,|rawIntervalUnassignedColumnCount π d σ v Finset.univ-
      ∑w:U,(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j))|<(n:ℝ)^(3/4:ℝ))→
    FirstVortexClassPreparedRetainedFullPackingOutcome P Sclass π Dv mm d m β ε Vort F hF θ lamAssign eps δlocal α bmatch ρ₀ ξ Δ a γ weight w σE t Jret →
    FirstVortexClassPreparedRetainedFullPackingOutcomeWithAllHubLoad P Sclass π Dv mm d m β ε Vort F hF θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w σE t Jret :=by
  obtain ⟨Nglobal,hGlobal⟩:=first_vortex_class_prepared_full_packing_precise_global ε θ δglobal ρ₀ lam lamAssign ζret α ξEdit m d hm hdlarge hε hθ hθ1 hδglobal hθδ Nret hNret hρhi hεsmall hlam hlampos hlam1 hd hspacing hα hρ₀ hθmax hsmall hεprecise
  obtain ⟨Nall,hAll⟩:=first_vortex_class_prepared_global_to_all_hub_precise ε θ δglobal ρ₀ lam lamAssign ζret α ξEdit m d hm hε hθ hθ1 hδglobal hθδ hmarg hρhi hεsmall hlam hlampos hlam1 hd hspacing hα hρ₀ hθmax hsmall hεprecise hlamθ
  refine ⟨max Nglobal Nall,?_⟩
  intro n K hn hK U _ _ P Sclass π Dv mm β Vort hreg hDv hρ hmm F hF δlocal bmatch eps ξ Δ a γ ρscale heps0 hepsAssign C₀ u hC hεα hlamα hu0 hu hUle hmax hΔlam hSP hγ ha hγcap hζ hζ0 hρscale hρscale0 hscale hnoshort weight w σE hedit hrows4 t Jret raw σ H A hrows hfixedInner hcolumnInner hboundary hcounts hgood hOcc hfixedAll hcolumnAll hPrep
  have hG0:=hGlobal n K (by omega) hK
  have hg1:firstVortexPreparedPreciseCombinedFin n=firstVortexPreparedAllHubAssembledFin n:=Subsingleton.elim _ _
  have hg2:firstVortexPreparedPreciseCombinedFin K=firstVortexPreparedAllHubAssembledFin K:=Subsingleton.elim _ _
  try rw [hg1] at hG0
  try rw [hg2] at hG0
  have hglobal:=hG0 U P Sclass π Dv mm β Vort hreg hDv hρ hmm F hF δlocal bmatch eps ξ Δ a γ ρscale heps0 hlamθ hepsAssign C₀ u hC hεα hlamα hu0 hu hUle hmax hΔlam hSP hγ ha hγcap hζ hζ0 hρscale hρscale0 hscale hnoshort weight w σE hedit hrows4 t Jret hrows hfixedInner hcolumnInner hcounts hgood hboundary hPrep
  have hA0:=hAll n K (by omega) hK
  have ha1:firstVortexPreparedAllHubPreciseFin n=firstVortexPreparedAllHubAssembledFin n:=Subsingleton.elim _ _
  have ha2:firstVortexPreparedAllHubPreciseFin K=firstVortexPreparedAllHubAssembledFin K:=Subsingleton.elim _ _
  try rw [ha1] at hA0
  try rw [ha2] at hA0
  exact hA0 U P Sclass π Dv mm β Vort hreg hDv hρ hmm F hF δlocal bmatch eps ξ Δ a γ ρscale heps0 hepsAssign C₀ u hC hεα hlamα hu0 hu hUle hmax hΔlam hSP hγ ha hγcap hζ hζ0 hρscale hρscale0 hscale hnoshort weight w σE hedit hrows4 t Jret hcounts hgood hOcc hfixedAll hcolumnAll hglobal
end Oberwolfach
