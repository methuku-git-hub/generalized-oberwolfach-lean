module

public import Oberwolfach.FirstVortexClassPreparedOrientedComplement
public import Oberwolfach.FirstVortexClassPreparedOrientedResidual
public import Oberwolfach.LongSelectedClassOrientedSourceComplementProof
public import Oberwolfach.FirstVortexPreparedOutcomeComplement

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexClassPreparedComplementProofFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_class_prepared_oriented_complement
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P Sclass:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (Dv mm d m:ℕ) (β ε:ℝ)
    (Vort:Vortex U P Dv β ε mm) (F:U→SimpleGraph (Fin n))
    (hF:∀w,(F w).IsRegularOfDegree 2) (θ lam eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ:ℝ)
    (weight:(Fin (m+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (σE:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) false) t)
    (hd:2≤d) (hclass:Sclass≤P):
    FirstVortexClassPreparedOrientedOutcomeWithResidualCompletion P Sclass π Dv mm d m β ε Vort F hF θ lam eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w σE t Jret →
    FirstVortexClassPreparedOrientedOutcomeWithComplement P Sclass π Dv mm d m β ε Vort F hF θ lam eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w σE t Jret :=by
  intro hPrep
  unfold FirstVortexClassPreparedOrientedOutcomeWithResidualCompletion at hPrep
  unfold FirstVortexClassPreparedOrientedOutcomeWithComplement
  have hdec0 : firstVortexClassPreparedResidualFin n = firstVortexClassPreparedComplementProofFin n := Subsingleton.elim _ _
  have hdec0K : firstVortexClassPreparedResidualFin K = firstVortexClassPreparedComplementProofFin K := Subsingleton.elim _ _
  have hdec1 : firstVortexClassPreparedComplementFin n = firstVortexClassPreparedComplementProofFin n := Subsingleton.elim _ _
  have hdec1K : firstVortexClassPreparedComplementFin K = firstVortexClassPreparedComplementProofFin K := Subsingleton.elim _ _
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
  have hP₀:P₀≤Sclass:=by intro x y h;exact h.1
  have hKclass:Kbad≤Sclass:=long_required_physical_graph_le_host Sclass P₀ Sel π d A D (fun x y=>Used.Adj x y) hP₀
  have hKbad:Kbad≤P:=le_trans hKclass hclass
  have hcont:=long_selected_class_oriented_source_complement hU F hF P Sclass π d m ℓ raw t Jret σE H A Kbad Used Del absorber δlocal
    (fun occupied Pack=>FirstVortexClassPrescribedAssignmentNoMarkedBudget P Sclass Del Used Kbad A π d σE t Jret H (2*α) bmatch ρ₀ θ ε lam occupied Pack ∧
      ∀w,((innerRequiredTargets H A (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
        (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) absorber occupied w).card:ℝ)≤(θ/1024)*n)
    ρ₀ θ δglobal hKbad hd
  have hdecC : longSelectedClassOrientedSourceComplementFin n = firstVortexClassPreparedComplementProofFin n := Subsingleton.elim _ _
  have hdecCK : longSelectedClassOrientedSourceComplementFin K = firstVortexClassPreparedComplementProofFin K := Subsingleton.elim _ _
  try rw [hdecC] at hcont
  try rw [hdecCK] at hcont
  exact hcont (M.map q) hsource'
end Oberwolfach
