module

public import Oberwolfach.FirstVortexClassPreparedBalancedDegrees
public import Oberwolfach.FirstVortexClassPreparedBalancedHost
public import Oberwolfach.LongClassBalancedMatchingResidualDegrees
public import Oberwolfach.LongRawMatchingAvoidsDeletedGraph
public import Oberwolfach.FirstVortexPreparedOutcomeComplement

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexClassPreparedBalancedDegreesProofFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_class_prepared_balanced_degrees
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P Sclass:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (Dv mm d m:ℕ) (β ε:ℝ)
    (Vort:Vortex U P Dv β ε mm) (F:U→SimpleGraph (Fin n))
    (hF:∀w,(F w).IsRegularOfDegree 2) (θ lam eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ:ℝ)
    (weight:(Fin (m+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (σE:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) false) t)
    (hd:2≤d) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x) (hclass:Sclass≤P):
    FirstVortexClassPreparedOrientedOutcomeWithBalancedHostCompletion P Sclass π Dv mm d m β ε Vort F hF θ lam eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w σE t Jret →
    FirstVortexClassPreparedOrientedOutcomeWithBalancedDegrees P Sclass π Dv mm d m β ε Vort F hF θ lam eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w σE t Jret :=by
  intro hPrep
  unfold FirstVortexClassPreparedOrientedOutcomeWithBalancedHostCompletion at hPrep
  unfold FirstVortexClassPreparedOrientedOutcomeWithBalancedDegrees
  have hdec0 : firstVortexClassPreparedBalancedHostFin n = firstVortexClassPreparedBalancedDegreesProofFin n := Subsingleton.elim _ _
  have hdec0K : firstVortexClassPreparedBalancedHostFin K = firstVortexClassPreparedBalancedDegreesProofFin K := Subsingleton.elim _ _
  have hdec1 : firstVortexClassPreparedBalancedDegreesFin n = firstVortexClassPreparedBalancedDegreesProofFin n := Subsingleton.elim _ _
  have hdec1K : firstVortexClassPreparedBalancedDegreesFin K = firstVortexClassPreparedBalancedDegreesProofFin K := Subsingleton.elim _ _
  try rw [hdec0] at hPrep
  try rw [hdec0K] at hPrep
  try rw [hdec1]
  try rw [hdec1K]
  intro ni hni ℓ raw selected Hret Wm Wo W Rsrc R hub Del δDel hDel hΔ hξ S T e Q q
  obtain ⟨M,hpos,hdisj,hinc,hlow,hup,hsourceCount,hsource⟩:=hPrep Del δDel hDel hΔ hξ
  refine ⟨M,hpos,hdisj,hinc,hlow,hup,hsourceCount,?_⟩
  intro D absorber Reserve X Z habs H A Used P₀ Sel Kbad
  intro Mhost hphysical hcorrect hbalance
  obtain ⟨hU,hsource'⟩:=hsource D absorber Reserve X Z habs Mhost hphysical hcorrect
  refine ⟨hU,?_⟩
  have hav := long_raw_surviving_matching_physical_rims_avoid_deleted_graph P Del π d m ℓ raw true true M
  have hdecA : instDecidableEqFin n = firstVortexClassPreparedBalancedDegreesProofFin n := Subsingleton.elim _ _
  have hdecAK : instDecidableEqFin K = firstVortexClassPreparedBalancedDegreesProofFin K := Subsingleton.elim _ _
  try rw [hdecA] at hav
  try rw [hdecAK] at hav
  have hcont:=long_class_balanced_matching_residual_degrees hU F hF P π d m ℓ σE t Jret H A Kbad Used Del absorber δlocal Sclass Mhost
    (fun occupied Pack=>FirstVortexClassPrescribedAssignmentNoMarkedBudget P Sclass Del Used Kbad A π d σE t Jret H (2*α) bmatch ρ₀ θ ε lam occupied Pack ∧
      ∀w,((innerRequiredTargets H A (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
        (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) absorber occupied w).card:ℝ)≤(θ/1024)*n)
    ρ₀ θ δglobal hd hnoshort hphysical hbalance hclass hcorrect hav
  have hdecC : longClassBalancedMatchingResidualFin n = firstVortexClassPreparedBalancedDegreesProofFin n := Subsingleton.elim _ _
  have hdecCK : longClassBalancedMatchingResidualFin K = firstVortexClassPreparedBalancedDegreesProofFin K := Subsingleton.elim _ _
  try rw [hdecC] at hcont
  try rw [hdecCK] at hcont
  exact hcont (M.map q) hsource'

end Oberwolfach
