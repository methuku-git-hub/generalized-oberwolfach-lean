module

public import Oberwolfach.FirstVortexPreparedOrientedComplement
public import Oberwolfach.FirstVortexPreparedOrientedResidual
public import Oberwolfach.LongSelectedOrientedSourceComplementProof
public import Oberwolfach.FirstVortexPreparedOutcomeComplement

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexPreparedOrientedComplementProofFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_prepared_oriented_complement
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (Dv mm d m:ℕ) (β ε:ℝ)
    (Vort:Vortex U P Dv β ε mm) (F:U→SimpleGraph (Fin n))
    (hF:∀w,(F w).IsRegularOfDegree 2) (θ lam eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ:ℝ)
    (weight:(Fin (m+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (σE:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) false) t)
    (hd:2≤d):
    FirstVortexPreparedOrientedOutcomeWithResidualCompletion P π Dv mm d m β ε Vort F hF θ lam eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w σE t Jret →
    FirstVortexPreparedOrientedOutcomeWithComplement P π Dv mm d m β ε Vort F hF θ lam eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w σE t Jret :=by
  intro hPrep
  unfold FirstVortexPreparedOrientedOutcomeWithResidualCompletion at hPrep
  unfold FirstVortexPreparedOrientedOutcomeWithComplement
  have hdec0 : firstVortexPreparedOrientedResidualFin n = firstVortexPreparedOrientedComplementProofFin n := Subsingleton.elim _ _
  have hdec0K : firstVortexPreparedOrientedResidualFin K = firstVortexPreparedOrientedComplementProofFin K := Subsingleton.elim _ _
  have hdec1 : firstVortexPreparedOrientedComplementFin n = firstVortexPreparedOrientedComplementProofFin n := Subsingleton.elim _ _
  have hdec1K : firstVortexPreparedOrientedComplementFin K = firstVortexPreparedOrientedComplementProofFin K := Subsingleton.elim _ _
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
  have hP₀:P₀≤P:=by intro x y h;exact h.1.1
  have hKbad:Kbad≤P:=long_required_physical_graph_le_host P P₀ Sel π d A D (fun x y=>Used.Adj x y) hP₀
  have hcont:=long_selected_oriented_source_complement hU F hF P π d m ℓ raw t Jret σE H A Kbad Used Del absorber δlocal
    (fun occupied Pack=>FirstVortexPrescribedAssignmentOutcome P Del Used Kbad A π d σE t Jret H α bmatch ρ₀ θ ε lam occupied Pack ∧
      ∀w,((innerRequiredTargets H A (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
        (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) absorber occupied w).card:ℝ)≤(θ/1024)*n)
    ρ₀ θ δglobal hKbad hd
  have hdecC : longSelectedOrientedSourceComplementFin n = firstVortexPreparedOrientedComplementProofFin n := Subsingleton.elim _ _
  have hdecCK : longSelectedOrientedSourceComplementFin K = firstVortexPreparedOrientedComplementProofFin K := Subsingleton.elim _ _
  try rw [hdecC] at hcont
  try rw [hdecCK] at hcont
  exact hcont (M.map q) hsource'
end Oberwolfach
