module

public import Oberwolfach.FirstVortexClassRetainedTargetCapacityFromLocalDegree
public import Oberwolfach.FirstVortexCapacityInputsFromCommonMatching
public import Oberwolfach.FirstVortexClassRetainedFullPackingTargetCapacity
public import Oberwolfach.LongSelectedRetainedSourceDynamicBad
public import Oberwolfach.LongSelectedRetainedSourceDynamicCapacity
public import Oberwolfach.LongSelectedRetainedSourceDynamicGlobalLoad
public import Oberwolfach.FirstVortexClassPreparedRetainedFullPackingOutcome
public import Oberwolfach.FirstVortexClassPreparedRetainedFullPackingCapacity
public import Oberwolfach.FirstVortexClassFullPackingTargetCapacity
public import Oberwolfach.FirstVortexClassPreparedRetainedFullPackingOutcome
public import Oberwolfach.FirstVortexClassPreparedOrientedCapacity
public import Oberwolfach.FirstVortexClassOrientedTargetCapacity
public import Oberwolfach.FirstVortexPreparedOrientedOutcome
public import Oberwolfach.FirstVortexPreparedOrientedCapacity
public import Oberwolfach.FirstVortexOrientedTargetCapacity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexPreparedPreciseCommonFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_class_prepared_full_packing_with_precise_common_capacity
    (ε θ ρ₀ lam lamAssign ξEdit δglobal α:ℝ) (m d:ℕ) (hm:0<m) (hε:0<ε) (hθ:0<θ) (hθ1:θ≤1)
    (hρhi:ρ₀≤1) (hεsmall:ε≤(ρ₀/4)/80000)
    (hlam:0≤lam) (hlampos:0<lam) (hlam1:lam≤1) (hd:0<d) (hspacing:1/(d:ℝ)≤θ/1024)
    (hα:0<α) (hρ₀:0<ρ₀) (hθmax:θ≤1/100)
    (hsmall:lam+ξEdit≤((ρ₀/4)/40000)*θ/4096)
    (hεprecise:ε≤((ρ₀/4)/40000)/8192) (hglobal:10*θ≤δglobal):
    ∃N:ℕ,∀n K:ℕ,N≤n→3≤K→∀(U:Type) [Fintype U] [DecidableEq U]
    (P Sclass:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (Dv mm:ℕ) (β:ℝ) (Vort:Vortex U P Dv β ε mm)
    (hreg:P.IsRegularOfDegree Dv) (hDv:0<Dv) (hρ:initialIndexDensity U Dv≤1) (hmm:0<mm)
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (δlocal bmatch eps ξ Δ a γ ζ:ℝ)
    (heps0:0≤eps) (hlamθ:lam≤θ)
    (hepsAssign:3*eps≤lam*(θ/(100*(K:ℝ)^2)))
    (C₀ u:ℝ) (hC:1≤C₀) (hεα:ε≤α/(1000*C₀)) (hlamα:lam≤α/128)
    (hu0:0≤u) (hu: u≤2*θ) (hUle:Fintype.card U≤n) (hmax:2*max a (4*γ)≤lam/3)
    (hΔlam:Δ≤lam/3)
    (hSP:Sclass≤P)
    (hγ:0≤γ) (ha:a≤lam/(10*d)) (hγcap:γ≤lam/(10*d))
    (hζ:ζ≤θ/4096) (hζ0:0≤ζ)
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
    (RetainedRestrictionLocalGood π d σ false t A H ζ Jret)→
    (∀u∈H,|rawIntervalUnassignedHubCountOn π d σ u A-
      (A.card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K m θ u g)-
        (∑j,longAssignedSpokeProbability F hF K m θ u j))|<(A.card:ℝ)^(3/4:ℝ))→
    (∀v∈A,|rawIntervalUnassignedColumnCount π d σ v H-
      ∑u∈H,(1-(∑g,longAssignedIntervalProbability F hF K m θ u g)-
        (∑j,longAssignedSpokeProbability F hF K m θ u j))|<(A.card:ℝ)^(3/4:ℝ))→
    (∀u g,|rawIntervalHubStartCount π d g σ u-(n:ℝ)*longAssignedIntervalProbability F hF K m θ u g/d|<(n:ℝ)^(3/4:ℝ)/d)→
    FirstVortexClassPreparedRetainedFullPackingOutcome P Sclass π Dv mm d m β ε Vort F hF θ lamAssign eps δlocal α bmatch ρ₀ ξ Δ a γ weight w σE t Jret →
    FirstVortexClassPreparedRetainedFullPackingOutcomeWithCapacity P Sclass π Dv mm d m β ε Vort F hF θ lamAssign eps δlocal α bmatch ρ₀ ξ Δ a γ weight w σE t Jret :=by
  obtain ⟨N,hN⟩:=first_vortex_class_full_packing_target_and_capacity_from_local_degree ε θ ρ₀ lam m d hm hε hθ hθ1 hρhi hεsmall hlam hlam1 hd hspacing
  have hAgeom:0<((ρ₀/4)/40000):=by positivity
  have hAgeom1:((ρ₀/4)/40000)≤1:=by linarith
  obtain ⟨Nprec,hNprec⟩:=first_vortex_capacity_inputs_from_common_matching α lam ε θ ξEdit ((ρ₀/4)/40000) δglobal d hα hlampos (by omega) hε.le hθ hθmax hAgeom hAgeom1 hεprecise hsmall hglobal
  refine ⟨max N Nprec,?_⟩
  intro n K hn hK U _ _ P Sclass π Dv mm β Vort hreg hDv hρ hmm F hF δlocal bmatch eps ξ Δ a γ ζ heps0 hlamθ hepsAssign C₀ u hC hεα hlamα hu0 hu hUle hmax hΔlam hSP hγ ha hγcap hζ hζ0 hnoshort weight w σE hedit hrows4 t Jret raw σ H A hrows hfixed hcolumn hcounts hPrep
  unfold FirstVortexClassPreparedRetainedFullPackingOutcome at hPrep
  unfold FirstVortexClassPreparedRetainedFullPackingOutcomeWithCapacity
  have hdec0 : firstVortexClassPreparedFullPackingFinRetained n = firstVortexPreparedPreciseCommonFin n := Subsingleton.elim _ _
  have hdec0K : firstVortexClassPreparedFullPackingFinRetained K = firstVortexPreparedPreciseCommonFin K := Subsingleton.elim _ _
  have hdec1 : firstVortexClassPreparedFullPackingCapacityFinRetained n = firstVortexPreparedPreciseCommonFin n := Subsingleton.elim _ _
  have hdec1K : firstVortexClassPreparedFullPackingCapacityFinRetained K = firstVortexPreparedPreciseCommonFin K := Subsingleton.elim _ _
  try rw [hdec0] at hPrep
  try rw [hdec0K] at hPrep
  try rw [hdec1]
  try rw [hdec1K]
  intro ni hni ℓ raw' selected Hret Wm Wo W Rsrc R hub Del δDel hDel hΔ hξ S T e Q q
  obtain ⟨M,hpos,hdisj,hinc,hlow,hup,hsourceCount,hsource⟩:=hPrep Del δDel hDel hΔ hξ
  refine ⟨M,hpos,hdisj,hinc,hlow,hup,hsourceCount,?_⟩
  intro D absorber Reserve X Z habs H' A' Used P₀ Sel Kbad Kplus
  have hcount:=hsourceCount Reserve X Z habs
  have hsource':=hsource D absorber Reserve X Z habs
  obtain ⟨hU,hsource'⟩:=hsource'
  have hN':=hN n K (by omega) (by omega)
  have hdecN : firstVortexClassTargetLocalDegreeFin n = firstVortexPreparedPreciseCommonFin n := Subsingleton.elim _ _
  have hdecNK : firstVortexClassTargetLocalDegreeFin K = firstVortexPreparedPreciseCommonFin K := Subsingleton.elim _ _
  try rw [hdecN] at hN'
  try rw [hdecNK] at hN'
  have hDelScale:δDel≤(lam/3)*n:=by
    have hh:=mul_le_mul_of_nonneg_right hΔlam (Nat.cast_nonneg n)
    exact hΔ.trans hh
  have hNprec' := hNprec n (by omega)
  have hdecPrec:instDecidableEqFin n=firstVortexPreparedPreciseCommonFin n:=Subsingleton.elim _ _
  have hdecPrecK:instDecidableEqFin K=firstVortexPreparedPreciseCommonFin K:=Subsingleton.elim _ _
  try rw [hdecPrec] at hNprec'
  try rw [hdecPrecK] at hNprec'
  have hprec0:=hNprec' U _ P Sclass Sel Del Dv mm β Vort π D σE true true R M
  have hdecSix:firstVortexPreparedPreciseCommonFin 6=instDecidableEqFin 6:=Subsingleton.elim _ _
  rw [hdecSix] at hedit
  have hprec:=hprec0 hSP hedit (by intro x hx y hy hxy; exact hxy) C₀ u a γ δDel hC hεα hlamα hu0 hu hγ hUle hmax hDel hDelScale (by convert hrows4 using 1 <;> congr! 12 <;> exact Subsingleton.elim _ _) hinc
    (fun Old Pack=>FirstVortexClassPrescribedAssignmentNoMarkedBudget P Sclass Del Used (Kplus Pack) A π d σE t Jret H (2*α) bmatch ρ₀ θ ε lamAssign Old Pack ∧ Pack=Used.edgeFinset)
    (fun Old Pack h=>h.2)
  refine ⟨hU,?_⟩
  refine hN'  U P π Dv mm β Vort hreg hDv hρ hmm σE Del.edgeFinset t Jret M F hF a γ ζ hγ ha hγcap hζ hζ0 hinc hrows hfixed hcolumn Kplus Used absorber δlocal hU
    Sclass Del bmatch lamAssign eps (2*α) hK hθmax heps0 hρ₀ (by positivity) hlamθ hepsAssign hnoshort hdisj hcounts hcount ?_ hsource'
  intro Old Pack h v
  have hh:=hprec.1 Old Pack h v
  convert hh using 1 <;> ring 
end Oberwolfach
