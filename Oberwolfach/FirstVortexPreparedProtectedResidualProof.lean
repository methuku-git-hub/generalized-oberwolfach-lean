module

public import Oberwolfach.FirstVortexPreparedProtectedGlobal
public import Oberwolfach.FirstVortexPreparedProtectedResidual
public import Oberwolfach.FirstVortexProtectedResidualContinuation
public import Oberwolfach.FirstVortexPreparedOutcomeResidual

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexPreparedProtectedResidualProofFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_prepared_protected_residual_completion
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (Dv mm d m:ℕ) (β ε:ℝ)
    (Vort:Vortex U P Dv β ε mm) (F:U→SimpleGraph (Fin n))
    (hF:∀w,(F w).IsRegularOfDegree 2) (θ lam eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ βfinal:ℝ)
    (weight:(Fin (m+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (σE:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) false) t)
    (hρ₀:0<ρ₀) (hb:0≤bmatch) (hbsmall:bmatch≤((ρ₀/4)/40000)/16) (hαb:α/16≤bmatch)
    (hθδ:10*θ≤δglobal) (hεδ:ε≤δglobal) (hβ:0<βfinal) (hβ1:βfinal≤1)
    (hδ:0<δglobal) (hδbound:δglobal≤(βfinal/100)^2)
    (hn:0<n) (hnβ:100/βfinal≤(n:ℝ)) (hnδ:2/Real.sqrt δglobal≤(n:ℝ)) (hu:Fintype.card U≤n)
    (hExt:∀Del:SimpleGraph (Fin n),(∀v,(Del.degree v:ℝ)≤Δ*n)→
      ∀u,IsExtendingList (fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σE (Sum.inl e)) x y ∧ ¬Del.Adj x y)
        (rawReservedSpokeList π d (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) u \
          (Vort.extendedVertices 1∪retainedFinalMarkedAt π d
            (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) t Jret u)) βfinal):
    FirstVortexPreparedProtectedOutcomeWithGlobalLoad P π Dv mm d m β ε Vort F hF θ lam eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w σE t Jret →
    FirstVortexPreparedProtectedOutcomeWithResidualCompletion P π Dv mm d m β ε Vort F hF θ lam eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w σE t Jret :=by
  intro hPrep
  unfold FirstVortexPreparedProtectedOutcomeWithGlobalLoad at hPrep
  unfold FirstVortexPreparedProtectedOutcomeWithResidualCompletion
  have hdec0 : firstVortexPreparedProtectedGlobalFin n = firstVortexPreparedProtectedResidualProofFin n := Subsingleton.elim _ _
  have hdec0K : firstVortexPreparedProtectedGlobalFin K = firstVortexPreparedProtectedResidualProofFin K := Subsingleton.elim _ _
  have hdec1 : firstVortexPreparedProtectedResidualFin n = firstVortexPreparedProtectedResidualProofFin n := Subsingleton.elim _ _
  have hdec1K : firstVortexPreparedProtectedResidualFin K = firstVortexPreparedProtectedResidualProofFin K := Subsingleton.elim _ _
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
  have hcont:=first_vortex_protected_residual_continuation P Del π d m ℓ σE t Jret F H A Kbad Used absorber
    δlocal ρ₀ θ ε lam α bmatch βfinal δglobal hρ₀ hb hbsmall hαb hθδ hεδ hβ hβ1 hδ hδbound hn hnβ hnδ hu hU
  have hdecC : firstVortexProtectedResidualContinuationFin n = firstVortexPreparedProtectedResidualProofFin n := Subsingleton.elim _ _
  have hdecCK : firstVortexProtectedResidualContinuationFin K = firstVortexPreparedProtectedResidualProofFin K := Subsingleton.elim _ _
  try rw [hdecC] at hcont
  try rw [hdecCK] at hcont
  exact hcont (hExt Del (fun v=>(hDel v).trans hΔ)) (M.map q) hsource'
end Oberwolfach
