module

public import Oberwolfach.FirstVortexClassRetainedFullPackingGlobalBoundaryProof
public import Oberwolfach.FirstVortexClassPreparedRetainedFullPackingCapacityProof
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
local instance firstVortexSingleLevelGlobalFinRetained (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_class_single_level_packing_to_global_load_retained
    (ε θ δglobal ρ₀ lam lamAssign ζret:ℝ) (m d:ℕ) (hm:0<m) (hdlarge:m+2≤d)
    (hε:0<ε) (hθ:0<θ) (hθ1:θ≤1) (hδglobal:0<δglobal) (hθδ:10*θ≤δglobal)
    (Nret:ℕ) (hNret:∀n:ℕ,Nret≤n→∀q errOrd:ℝ,
      q≤1/((m:ℝ)+1)→errOrd≤θ*n→
      (n:ℝ)*q/d+(((m+1)*d-1:ℕ):ℝ)*(2*((n:ℝ)^(3/4:ℝ)/d)+ζret*n)+errOrd≤4*θ*n)
    (hρhi:ρ₀≤1) (hεsmall:ε≤(ρ₀/4)/80000)
    (hlam:0≤lam) (hlam1:lam≤1) (hd:0<d) (hspacing:1/(d:ℝ)≤θ/1024):
    ∃N:ℕ,∀n K:ℕ,N≤n→3≤K→∀(U:Type) [Fintype U] [DecidableEq U]
    (P Sclass:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (Dv mm:ℕ) (β:ℝ) (Vort:Vortex U P Dv β ε mm)
    (hreg:P.IsRegularOfDegree Dv) (hDv:0<Dv) (hρ:initialIndexDensity U Dv≤1) (hmm:0<mm)
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (δlocal α bmatch eps ξ Δ a γ ρscale:ℝ)
    (hθmax:θ≤1/100) (heps0:0≤eps) (hρ₀:0<ρ₀) (hα:0<α) (hlamθ:lam≤θ)
    (hepsAssign:3*eps≤lam*(θ/(100*(K:ℝ)^2)))
    (hαsmall:(2*α)/16≤((ρ₀/4)/40000)*θ/1024) (hαglobal:2*α≤4*δglobal)
    (hγ:0≤γ) (ha:a≤lam/(10*d)) (hγcap:γ≤lam/(10*d))
    (hζ:ζret≤θ/4096) (hζ0:0≤ζret) (hρscale:ρscale≤θ/4096) (hρscale0:0≤ρscale)
    (hscale:max a γ*n≤ρscale*(Vort.extendedVertices 1).card)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (weight:(Fin (m+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (σE:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
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
    FirstVortexClassPreparedRetainedFullPackingOutcome P Sclass π Dv mm d m β ε Vort F hF θ lamAssign eps δlocal α bmatch ρ₀ ξ Δ a γ weight w σE t Jret →
    FirstVortexClassPreparedRetainedFullPackingOutcomeWithGlobalLoad P Sclass π Dv mm d m β ε Vort F hF θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w σE t Jret :=by
  obtain ⟨Ncap,hCap⟩:=first_vortex_class_prepared_full_packing_with_capacity_retained ε θ ρ₀ lam lamAssign m d hm hε hθ hθ1 hρhi hεsmall hlam hlam1 hd hspacing
  obtain ⟨Nglobal,hGlobal⟩:=first_vortex_class_full_packing_with_boundary_global_load_retained ε θ δglobal ρ₀ lam lamAssign ζret m d hm hdlarge hε hθ hθ1 hδglobal hθδ Nret hNret hρhi hεsmall hlam hlam1 hd hspacing
  refine ⟨max Ncap Nglobal,?_⟩
  intro n K hn hK U _ _ P Sclass π Dv mm β Vort hreg hDv hρ hmm F hF δlocal α bmatch eps ξ Δ a γ ρscale
    hθmax heps0 hρ₀ hα hlamθ hepsAssign hαsmall hαglobal hγ ha hγcap hζ hζ0 hρscale hρscale0 hscale hnoshort weight w σE t Jret raw σ H A hrows hfixed hcolumn hcounts hgood hboundary hPrep
  have hcN:firstVortexClassPreparedFullPackingCapacityProofFinRetained n=firstVortexSingleLevelGlobalFinRetained n:=Subsingleton.elim _ _
  have hcK:firstVortexClassPreparedFullPackingCapacityProofFinRetained K=firstVortexSingleLevelGlobalFinRetained K:=Subsingleton.elim _ _
  have hgN:firstVortexClassFullPackingGlobalBoundaryFinRetained n=firstVortexSingleLevelGlobalFinRetained n:=Subsingleton.elim _ _
  have hgK:firstVortexClassFullPackingGlobalBoundaryFinRetained K=firstVortexSingleLevelGlobalFinRetained K:=Subsingleton.elim _ _
  try rw [hcN] at hCap
  try rw [hcK] at hCap
  try rw [hgN] at hGlobal
  try rw [hgK] at hGlobal
  have hcapacity:=hCap n K (by omega) hK U P Sclass π Dv mm β Vort hreg hDv hρ hmm F hF δlocal α bmatch eps ξ Δ a γ ζret
    hθmax heps0 hρ₀ hα hlamθ hepsAssign hαsmall hγ ha hγcap hζ hζ0 hnoshort weight w σE t Jret hrows hfixed hcolumn hcounts hPrep
  exact hGlobal n K (by omega) hK U P Sclass π Dv mm β Vort hreg hDv hρ hmm F hF δlocal α bmatch eps ξ Δ a γ ρscale
    hθmax heps0 hρ₀ hα hlamθ hepsAssign hαsmall hαglobal hγ ha hγcap hζ hζ0 hρscale hρscale0 hscale hnoshort weight w σE t Jret
    hrows hfixed hcolumn hcounts hgood hboundary hcapacity
end Oberwolfach
