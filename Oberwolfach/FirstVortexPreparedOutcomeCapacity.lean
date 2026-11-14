module

public import Oberwolfach.FirstVortexPreparedCommonOutcomeWithCapacity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexPreparedOutcomeCapacityFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_prepared_outcome_with_capacity
    (ε θ ρ₀ lam:ℝ) (m d:ℕ) (hm:0<m) (hε:0<ε) (hθ:0<θ) (hθ1:θ≤1)
    (hρhi:ρ₀≤1) (hεsmall:ε≤(ρ₀/4)/80000)
    (hlam:0≤lam) (hlam1:lam≤1) (hd:0<d) (hspacing:1/(d:ℝ)≤θ/1024):
    ∃N:ℕ,∀n K:ℕ,N≤n→3≤K→∀(U:Type) [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (Dv mm:ℕ) (β:ℝ) (Vort:Vortex U P Dv β ε mm)
    (hreg:P.IsRegularOfDegree Dv) (hDv:0<Dv) (hρ:initialIndexDensity U Dv≤1) (hmm:0<mm)
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (δlocal α bmatch eps ξ Δ a γ ζ:ℝ)
    (hθmax:θ≤1/100) (heps0:0≤eps) (hρ₀:0<ρ₀) (hα:0<α) (hlamθ:lam≤θ)
    (hepsAssign:3*eps≤lam*(θ/(100*(K:ℝ)^2)))
    (hαsmall:α/16≤((ρ₀/4)/40000)*θ/1024)
    (hγ:0≤γ) (ha:a≤lam/(10*d)) (hγcap:γ≤lam/(10*d))
    (hζ:ζ≤θ/4096) (hζ0:0≤ζ)
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
    (RetainedRestrictionLocalGood π d σ false t A H ζ Jret)→
    (∀u∈H,|rawIntervalUnassignedHubCountOn π d σ u A-
      (A.card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K m θ u g)-
        (∑j,longAssignedSpokeProbability F hF K m θ u j))|<(A.card:ℝ)^(3/4:ℝ))→
    (∀v∈A,|rawIntervalUnassignedColumnCount π d σ v H-
      ∑u∈H,(1-(∑g,longAssignedIntervalProbability F hF K m θ u g)-
        (∑j,longAssignedSpokeProbability F hF K m θ u j))|<(A.card:ℝ)^(3/4:ℝ))→
    (∀u g,|rawIntervalHubStartCount π d g σ u-(n:ℝ)*longAssignedIntervalProbability F hF K m θ u g/d|<(n:ℝ)^(3/4:ℝ)/d)→
    FirstVortexPreparedCommonOutcome P π Dv mm d m β ε Vort F hF θ lam eps δlocal α bmatch ρ₀ ξ Δ a γ weight w σE t Jret →
    FirstVortexPreparedCommonOutcomeWithCapacity P π Dv mm d m β ε Vort F hF θ lam eps δlocal α bmatch ρ₀ ξ Δ a γ weight w σE t Jret :=by
  obtain ⟨N,hN⟩:=first_vortex_source_matching_target_and_capacity ε θ ρ₀ lam m d hm hε hθ hθ1 hρhi hεsmall hlam hlam1 hd hspacing
  refine ⟨N,?_⟩
  intro n K hn hK U _ _ P π Dv mm β Vort hreg hDv hρ hmm F hF δlocal α bmatch eps ξ Δ a γ ζ hθmax heps0 hρ₀ hα hlamθ hepsAssign hαsmall hγ ha hγcap hζ hζ0 hnoshort weight w σE t Jret raw σ H A hrows hfixed hcolumn hcounts hPrep
  unfold FirstVortexPreparedCommonOutcome at hPrep
  unfold FirstVortexPreparedCommonOutcomeWithCapacity
  have hdec0 : firstVortexPreparedOutcomeFin n = firstVortexPreparedOutcomeCapacityFin n := Subsingleton.elim _ _
  have hdec0K : firstVortexPreparedOutcomeFin K = firstVortexPreparedOutcomeCapacityFin K := Subsingleton.elim _ _
  have hdec1 : firstVortexPreparedCapacityOutcomeFin n = firstVortexPreparedOutcomeCapacityFin n := Subsingleton.elim _ _
  have hdec1K : firstVortexPreparedCapacityOutcomeFin K = firstVortexPreparedOutcomeCapacityFin K := Subsingleton.elim _ _
  try rw [hdec0] at hPrep
  try rw [hdec0K] at hPrep
  try rw [hdec1]
  try rw [hdec1K]
  intro ni hni ℓ raw' selected Hret Wm Wo W Rsrc R hub Del δDel hDel hΔ hξ S T e Q q
  obtain ⟨M,hpos,hdisj,hinc,hlow,hup,hsourceCount,hsource⟩:=hPrep Del δDel hDel hΔ hξ
  refine ⟨M,hpos,hdisj,hinc,hlow,hup,hsourceCount,?_⟩
  intro D absorber Reserve X Z habs H' A' Used P₀ Sel Kbad
  have hcount:=hsourceCount Reserve X Z habs
  have hsource':=hsource D absorber Reserve X Z habs
  obtain ⟨hU,hsource'⟩:=hsource'
  have hN':=hN n K hn (by omega)
  have hdecN : firstVortexSourceTargetCapacityFin n = firstVortexPreparedOutcomeCapacityFin n := Subsingleton.elim _ _
  have hdecNK : firstVortexSourceTargetCapacityFin K = firstVortexPreparedOutcomeCapacityFin K := Subsingleton.elim _ _
  try rw [hdecN] at hN'
  try rw [hdecNK] at hN'
  refine ⟨hU,?_⟩
  refine hN' U P π Dv mm β Vort hreg hDv hρ hmm σE Del.edgeFinset t Jret M F hF a γ ζ hγ ha hγcap hζ hζ0 hinc hrows hfixed hcolumn Kbad Used absorber δlocal hU
    (FirstVortexPrescribedAssignmentOutcome P Del Used Kbad A π d σE t Jret H α bmatch ρ₀ θ ε lam)
    eps α hK hθmax heps0 hρ₀ hα hlamθ hepsAssign hαsmall hnoshort hdisj hcounts hcount ?_ hsource'
  intro occupied Pack hh
  exact hh.1
end Oberwolfach
