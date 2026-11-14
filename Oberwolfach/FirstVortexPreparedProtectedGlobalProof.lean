module

public import Oberwolfach.FirstVortexPreparedProtectedGlobal
public import Oberwolfach.FirstVortexProtectedResidualUpper
public import Oberwolfach.FirstVortexProtectedGlobalLoad
public import Oberwolfach.FirstVortexPreparedOutcomeGlobalLoad

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexPreparedProtectedGlobalProofFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_prepared_protected_with_global_load
    (ε θ δglobal ρ₀ lam ζret:ℝ) (m d:ℕ) (hm:0<m) (hdlarge:m+2≤d)
    (hε:0<ε) (hθ:0<θ) (hθ1:θ≤1) (hδglobal:0<δglobal) (hθδ:10*θ≤δglobal)
    (hmarg:4/(m:ℝ)≤δglobal/4)
    (Nret:ℕ) (hNret:∀n:ℕ,Nret≤n→∀q errOrd:ℝ,
      q≤1/((m:ℝ)+1)→errOrd≤θ*n→
      (n:ℝ)*q/d+(((m+1)*d-1:ℕ):ℝ)*(2*((n:ℝ)^(3/4:ℝ)/d)+ζret*n)+errOrd≤4*θ*n)
    (hρhi:ρ₀≤1) (hεsmall:ε≤(ρ₀/4)/80000)
    (hlam:0≤lam) (hlam1:lam≤1) (hd:0<d) (hspacing:1/(d:ℝ)≤θ/1024):
    ∃N:ℕ,∀n K:ℕ,N≤n→3≤K→∀(U:Type) [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (Dv mm:ℕ) (β:ℝ) (Vort:Vortex U P Dv β ε mm)
    (hreg:P.IsRegularOfDegree Dv) (hDv:0<Dv) (hρ:initialIndexDensity U Dv≤1) (hmm:0<mm)
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (δlocal α bmatch eps ξ Δ a γ ρscale:ℝ)
    (hθmax:θ≤1/100) (heps0:0≤eps) (hρ₀:0<ρ₀) (hα:0<α) (hlamθ:lam≤θ)
    (hepsAssign:3*eps≤lam*(θ/(100*(K:ℝ)^2)))
    (hαsmall:α/16≤((ρ₀/4)/40000)*θ/1024) (hαglobal:α≤4*δglobal)
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
    (∀v,((rawIntervalExtendedAnyHubSet π d σ v).card:ℝ)≤4*(Fintype.card U:ℝ)/(m:ℝ)+4*(n:ℝ)^(3/4:ℝ))→
    FirstVortexPreparedProtectedOutcomeWithCapacity P π Dv mm d m β ε Vort F hF θ lam eps δlocal α bmatch ρ₀ ξ Δ a γ weight w σE t Jret →
    FirstVortexPreparedProtectedOutcomeWithGlobalLoad P π Dv mm d m β ε Vort F hF θ lam eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w σE t Jret :=by
  obtain ⟨Nglobal,hGlobal⟩:=first_vortex_protected_global_prescribed_load ε θ δglobal d hε hθ hθ1 hδglobal hθδ hd
  refine ⟨max (max Nglobal Nret) 1,?_⟩
  intro n K hn hK U _ _ P π Dv mm β Vort hreg hDv hρ hmm F hF δlocal α bmatch eps ξ Δ a γ ρscale hθmax heps0 hρ₀ hα hlamθ hepsAssign hαsmall hαglobal hγ ha hγcap hζ hζ0 hρscale hρscale0 hscale hnoshort weight w σE t Jret raw σ H A hrows hfixed hcolumn hcounts hgood hOcc hPrep
  unfold FirstVortexPreparedProtectedOutcomeWithCapacity at hPrep
  unfold FirstVortexPreparedProtectedOutcomeWithGlobalLoad
  have hdec0 : firstVortexPreparedProtectedCapacityFin n = firstVortexPreparedProtectedGlobalProofFin n := Subsingleton.elim _ _
  have hdec0K : firstVortexPreparedProtectedCapacityFin K = firstVortexPreparedProtectedGlobalProofFin K := Subsingleton.elim _ _
  have hdec1 : firstVortexPreparedProtectedGlobalFin n = firstVortexPreparedProtectedGlobalProofFin n := Subsingleton.elim _ _
  have hdec1K : firstVortexPreparedProtectedGlobalFin K = firstVortexPreparedProtectedGlobalProofFin K := Subsingleton.elim _ _
  try rw [hdec0] at hPrep
  try rw [hdec0K] at hPrep
  try rw [hdec1]
  try rw [hdec1K]
  intro ni hni ℓ raw' selected Hret Wm Wo W Rsrc R hub Del δDel hDel hΔ hξ S T e Q q
  obtain ⟨M,hpos,hdisj,hinc,hlow,hup,hsourceCount,hsource⟩:=hPrep Del δDel hDel hΔ hξ
  refine ⟨M,hpos,hdisj,hinc,hlow,hup,hsourceCount,?_⟩
  intro D absorber Reserve X Z habs H' A' Used P₀ Sel Kbad
  have hcount:=hsourceCount Reserve X Z habs
  obtain ⟨hU,hsource'⟩:=hsource D absorber Reserve X Z habs
  have hUpper:=first_vortex_protected_residual_upper m d hm hdlarge θ hθ hθmax ζret Nret hNret n K (by omega) (by omega) hK
  have hdecU : firstVortexProtectedResidualUpperFin n = firstVortexPreparedProtectedGlobalProofFin n := Subsingleton.elim _ _
  have hdecUK : firstVortexProtectedResidualUpperFin K = firstVortexPreparedProtectedGlobalProofFin K := Subsingleton.elim _ _
  try rw [hdecU] at hUpper
  try rw [hdecUK] at hUpper
  have hup:=hUpper U P π σE hnoshort Del.edgeFinset t Jret M F hF eps lam a γ heps0 hγ hlam hlamθ hepsAssign ha hγcap hdisj hinc hcounts hgood hcount H A Kbad Used absorber δlocal ρ₀ hU
    (fun occupied Pack=>FirstVortexPrescribedAssignmentOutcome P Del Used Kbad A π d σE t Jret H α bmatch ρ₀ θ ε lam occupied Pack ∧
      ∀w,((innerRequiredTargets H A (rawReservedSpokeList π d σ) (retainedFinalMarkedAt π d σ t Jret) absorber occupied w).card:ℝ)≤(θ/1024)*n) hsource'
  have hG:=hGlobal n K (by omega) (by omega)
  have hdecG : firstVortexProtectedGlobalLoadFin n = firstVortexPreparedProtectedGlobalProofFin n := Subsingleton.elim _ _
  have hdecGK : firstVortexProtectedGlobalLoadFin K = firstVortexPreparedProtectedGlobalProofFin K := Subsingleton.elim _ _
  try rw [hdecG] at hG
  try rw [hdecGK] at hG
  refine ⟨hU,?_⟩
  refine hG U P π m hm ℓ Dv mm β Vort hreg hDv hρ hmm σE Del.edgeFinset t Jret M F hF a γ ζret ρscale hγ hζ hζ0 hρscale hρscale0 hscale hmarg hOcc hinc hrows hfixed hcolumn Kbad Used absorber δlocal ρ₀ hU
    (fun occupied Pack=>FirstVortexPrescribedAssignmentOutcome P Del Used Kbad A π d σE t Jret H α bmatch ρ₀ θ ε lam occupied Pack ∧
      ∀w,((innerRequiredTargets H A (rawReservedSpokeList π d σ) (retainedFinalMarkedAt π d σ t Jret) absorber occupied w).card:ℝ)≤(θ/1024)*n) ?_ hup
  intro occupied Pack hh v
  have hbad:=hh.1.1 v
  have hn0:(0:ℝ)≤n:=by positivity
  have hcoef:α/16≤δglobal/4:=by linarith
  have hmul:=mul_le_mul_of_nonneg_right hcoef hn0
  nlinarith
end Oberwolfach
