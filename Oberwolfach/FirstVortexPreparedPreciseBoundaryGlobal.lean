module

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
local instance firstVortexPreparedPreciseGlobalFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_class_full_packing_with_precise_boundary_global_load
    (ε θ δglobal ρ₀ lam lamAssign ζret α ξEdit:ℝ) (m d:ℕ) (hm:0<m) (hdlarge:m+2≤d)
    (hε:0<ε) (hθ:0<θ) (hθ1:θ≤1) (hδglobal:0<δglobal) (hθδ:10*θ≤δglobal)
    (Nret:ℕ) (hNret:∀n:ℕ,Nret≤n→∀q errOrd:ℝ,
      q≤1/((m:ℝ)+1)→errOrd≤θ*n→
      (n:ℝ)*q/d+(((m+1)*d-1:ℕ):ℝ)*(2*((n:ℝ)^(3/4:ℝ)/d)+ζret*n)+errOrd≤4*θ*n)
    (hρhi:ρ₀≤1) (hεsmall:ε≤(ρ₀/4)/80000)
    (hlam:0≤lam) (hlampos:0<lam) (hlam1:lam≤1) (hd:0<d) (hspacing:1/(d:ℝ)≤θ/1024)
    (hα:0<α) (hρ₀:0<ρ₀) (hθmax:θ≤1/100)
    (hsmall:lam+ξEdit≤((ρ₀/4)/40000)*θ/4096)
    (hεprecise:ε≤((ρ₀/4)/40000)/8192):
    ∃N:ℕ,∀n K:ℕ,N≤n→3≤K→∀(U:Type) [Fintype U] [DecidableEq U]
    (P Sclass:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (Dv mm:ℕ) (β:ℝ) (Vort:Vortex U P Dv β ε mm)
    (hreg:P.IsRegularOfDegree Dv) (hDv:0<Dv) (hρ:initialIndexDensity U Dv≤1) (hmm:0<mm)
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (δlocal bmatch eps ξ Δ a γ ρscale:ℝ)
    (heps0:0≤eps) (hlamθ:lam≤θ)
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
    (∀u g,|rawIntervalHubStartCount π d g σ u-(n:ℝ)*longAssignedIntervalProbability F hF K m θ u g/d|<(n:ℝ)^(3/4:ℝ)/d)→
    (RetainedRestrictionGood π d σ false t (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζret Jret)→
    (∀v,((rawIntervalBoundaryHubSet π d σ Finset.univ v).card:ℝ)≤
      4*(Fintype.card U:ℝ)/d+4*(n:ℝ)^(3/4:ℝ))→
    FirstVortexClassPreparedRetainedFullPackingOutcomeWithCapacity P Sclass π Dv mm d m β ε Vort F hF θ lamAssign eps δlocal α bmatch ρ₀ ξ Δ a γ weight w σE t Jret →
    FirstVortexClassPreparedRetainedFullPackingOutcomeWithGlobalLoad P Sclass π Dv mm d m β ε Vort F hF θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w σE t Jret :=by
  obtain ⟨Nglobal,hGlobal⟩:=first_vortex_dynamic_global_prescribed_load_from_boundary_retained ε θ δglobal d hε hθ hθ1 hδglobal hθδ hd hspacing
  have hAgeom:0<((ρ₀/4)/40000):=by positivity
  have hAgeom1:((ρ₀/4)/40000)≤1:=by linarith
  obtain ⟨Nprec,hNprec⟩:=first_vortex_capacity_inputs_from_common_matching α lam ε θ ξEdit ((ρ₀/4)/40000) δglobal d hα hlampos (by omega) hε.le hθ hθmax hAgeom hAgeom1 hεprecise hsmall hθδ
  refine ⟨max (max (max Nglobal Nret) Nprec) 1,?_⟩
  intro n K hn hK U _ _ P Sclass π Dv mm β Vort hreg hDv hρ hmm F hF δlocal bmatch eps ξ Δ a γ ρscale heps0 hlamθ hepsAssign C₀ u hC hεα hlamα hu0 hu hUle hmax hΔlam hSP hγ ha hγcap hζ hζ0 hρscale hρscale0 hscale hnoshort weight w σE hedit hrows4 t Jret raw σ H A hrows hfixed hcolumn hcounts hgood hboundary hPrep
  unfold FirstVortexClassPreparedRetainedFullPackingOutcomeWithCapacity at hPrep
  unfold FirstVortexClassPreparedRetainedFullPackingOutcomeWithGlobalLoad
  have hdec0 : firstVortexClassPreparedFullPackingCapacityFinRetained n = firstVortexPreparedPreciseGlobalFin n := Subsingleton.elim _ _
  have hdec0K : firstVortexClassPreparedFullPackingCapacityFinRetained K = firstVortexPreparedPreciseGlobalFin K := Subsingleton.elim _ _
  have hdec1 : firstVortexClassPreparedFullPackingGlobalFinRetained n = firstVortexPreparedPreciseGlobalFin n := Subsingleton.elim _ _
  have hdec1K : firstVortexClassPreparedFullPackingGlobalFinRetained K = firstVortexPreparedPreciseGlobalFin K := Subsingleton.elim _ _
  try rw [hdec0] at hPrep
  try rw [hdec0K] at hPrep
  try rw [hdec1]
  try rw [hdec1K]
  intro ni hni ℓ raw' selected Hret Wm Wo W Rsrc R hub Del δDel hDel hΔ hξ S T e Q q
  obtain ⟨M,hpos,hdisj,hinc,hlow,hup,hsourceCount,hsource⟩:=hPrep Del δDel hDel hΔ hξ
  refine ⟨M,hpos,hdisj,hinc,hlow,hup,hsourceCount,?_⟩
  intro D absorber Reserve X Z habs H' A' Used P₀ Sel Kbad Kplus
  have hcount:=hsourceCount Reserve X Z habs
  obtain ⟨hU,hsource'⟩:=hsource D absorber Reserve X Z habs
  have hUpper:=first_vortex_dynamic_residual_upper_retained m d hm hdlarge θ hθ hθmax ζret Nret hNret n K (by omega) (by omega) hK
  have hdecU : firstVortexDynamicResidualUpperFinRetained n = firstVortexPreparedPreciseGlobalFin n := Subsingleton.elim _ _
  have hdecUK : firstVortexDynamicResidualUpperFinRetained K = firstVortexPreparedPreciseGlobalFin K := Subsingleton.elim _ _
  try rw [hdecU] at hUpper
  try rw [hdecUK] at hUpper
  have hup:=hUpper U P π σE hnoshort Del.edgeFinset t Jret M F hF eps lam a γ heps0 hγ hlam hlamθ hepsAssign ha hγcap hdisj hinc hcounts hgood hcount H A Kplus Used absorber δlocal ρ₀ hU
    (fun occupied Pack=>(FirstVortexClassPrescribedAssignmentNoMarkedBudget P Sclass Del Used (Kplus Pack) A π d σE t Jret H (2*α) bmatch ρ₀ θ ε lamAssign occupied Pack ∧ Pack=Used.edgeFinset) ∧
      ∀w,((innerRequiredTargets H A (rawReservedSpokeList π d σ) (retainedFinalMarkedAt π d σ t Jret) absorber occupied w).card:ℝ)≤(θ/1024)*n) hsource'
  have hG:=hGlobal n K (by omega) (by omega)
  have hdecG : firstVortexDynamicGlobalBoundaryFin n = firstVortexPreparedPreciseGlobalFin n := Subsingleton.elim _ _
  have hdecGK : firstVortexDynamicGlobalBoundaryFin K = firstVortexPreparedPreciseGlobalFin K := Subsingleton.elim _ _
  try rw [hdecG] at hG
  try rw [hdecGK] at hG
  have hDelScale:δDel≤(lam/3)*n:=by
    have hh:=mul_le_mul_of_nonneg_right hΔlam (Nat.cast_nonneg n)
    exact hΔ.trans hh
  have hNprec' := hNprec n (by omega)
  have hdecPrec:instDecidableEqFin n=firstVortexPreparedPreciseGlobalFin n:=Subsingleton.elim _ _
  have hdecPrecK:instDecidableEqFin K=firstVortexPreparedPreciseGlobalFin K:=Subsingleton.elim _ _
  try rw [hdecPrec] at hNprec'
  try rw [hdecPrecK] at hNprec'
  have hprec0:=hNprec' U _ P Sclass Sel Del Dv mm β Vort π D σE true true R M
  have hdecSix:firstVortexPreparedPreciseGlobalFin 6=instDecidableEqFin 6:=Subsingleton.elim _ _
  rw [hdecSix] at hedit
  have hprec:=hprec0 hSP hedit (by intro x hx y hy hxy; exact hxy) C₀ u a γ δDel hC hεα hlamα hu0 hu hγ hUle hmax hDel hDelScale (by convert hrows4 using 1 <;> congr! 12 <;> exact Subsingleton.elim _ _) hinc
    (fun Old Pack=>FirstVortexClassPrescribedAssignmentNoMarkedBudget P Sclass Del Used (Kplus Pack) A π d σE t Jret H (2*α) bmatch ρ₀ θ ε lamAssign Old Pack ∧ Pack=Used.edgeFinset)
    (fun Old Pack h=>h.2)
  refine ⟨hU,?_⟩
  refine hG U P π m hm ℓ Dv mm β Vort hreg hDv hρ hmm σE Del.edgeFinset t Jret M F hF a γ ζret ρscale hγ hζ hζ0 hρscale hρscale0 hscale hboundary hinc hrows hfixed hcolumn Kplus Used absorber δlocal ρ₀ hU
    (fun occupied Pack=>(FirstVortexClassPrescribedAssignmentNoMarkedBudget P Sclass Del Used (Kplus Pack) A π d σE t Jret H (2*α) bmatch ρ₀ θ ε lamAssign occupied Pack ∧ Pack=Used.edgeFinset) ∧
      ∀w,((innerRequiredTargets H A (rawReservedSpokeList π d σ) (retainedFinalMarkedAt π d σ t Jret) absorber occupied w).card:ℝ)≤(θ/1024)*n) ?_ hup
  intro occupied Pack hh v
  exact hprec.2 occupied Pack hh.1 v
end Oberwolfach
