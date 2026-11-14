module

public import Oberwolfach.FirstVortexPreparedProtectedSpokes
public import Oberwolfach.LongSelectedProtectedSourceSpokesProof
public import Oberwolfach.FirstVortexPreparedProtectedComplement
public import Oberwolfach.FirstVortexPreparedProtectedResidual
public import Oberwolfach.LongSelectedProtectedSourceComplementProof
public import Oberwolfach.FirstVortexPreparedOutcomeComplement

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexPreparedProtectedSpokesProofFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_prepared_protected_spokes
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (Dv mm d m:ℕ) (β ε:ℝ)
    (Vort:Vortex U P Dv β ε mm) (F:U→SimpleGraph (Fin n))
    (hF:∀w,(F w).IsRegularOfDegree 2) (θ lam eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ:ℝ)
    (weight:(Fin (m+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (σE:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) false) t)
    (hd:2≤d) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x):
    FirstVortexPreparedProtectedOutcomeWithComplement P π Dv mm d m β ε Vort F hF θ lam eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w σE t Jret →
    FirstVortexPreparedProtectedOutcomeWithSpokes P π Dv mm d m β ε Vort F hF θ lam eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w σE t Jret :=by
  intro hPrep
  unfold FirstVortexPreparedProtectedOutcomeWithComplement at hPrep
  unfold FirstVortexPreparedProtectedOutcomeWithSpokes
  have hdec0 : firstVortexPreparedProtectedComplementFin n = firstVortexPreparedProtectedSpokesProofFin n := Subsingleton.elim _ _
  have hdec0K : firstVortexPreparedProtectedComplementFin K = firstVortexPreparedProtectedSpokesProofFin K := Subsingleton.elim _ _
  have hdec1 : firstVortexPreparedProtectedSpokesFin n = firstVortexPreparedProtectedSpokesProofFin n := Subsingleton.elim _ _
  have hdec1K : firstVortexPreparedProtectedSpokesFin K = firstVortexPreparedProtectedSpokesProofFin K := Subsingleton.elim _ _
  try rw [hdec0] at hPrep
  try rw [hdec0K] at hPrep
  try rw [hdec1]
  try rw [hdec1K]
  intro ni hni ℓ raw selected Hret Wm Wo W Rsrc R hub Del δDel hDel hΔ hξ S T e Q q
  obtain ⟨M,hpos,hdisj,hinc,hlow,hup,hsourceCount,hsource⟩:=hPrep Del δDel hDel hΔ hξ
  refine ⟨M,hpos,hdisj,hinc,hlow,hup,hsourceCount,?_⟩
  intro D absorber Reserve X Z habs H A Used P₀ Sel Kbad
  obtain ⟨hU,hsource'⟩:=hsource D absorber Reserve X Z habs
  refine ⟨hU,?_⟩
  have hcont:=long_selected_protected_source_spokes hU F hF P π d m ℓ raw t Jret σE H A Kbad Used Del absorber δlocal
    (fun occupied Pack=>FirstVortexPrescribedAssignmentOutcome P Del Used Kbad A π d σE t Jret H α bmatch ρ₀ θ ε lam occupied Pack ∧
      ∀w,((innerRequiredTargets H A (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
        (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) absorber occupied w).card:ℝ)≤(θ/1024)*n)
    ρ₀ θ δglobal hd hnoshort
  have hdecC : longProtectedSourceSpokesFin n = firstVortexPreparedProtectedSpokesProofFin n := Subsingleton.elim _ _
  have hdecCK : longProtectedSourceSpokesFin K = firstVortexPreparedProtectedSpokesProofFin K := Subsingleton.elim _ _
  try rw [hdecC] at hcont
  try rw [hdecCK] at hcont
  exact hcont (M.map q) hsource'
end Oberwolfach
