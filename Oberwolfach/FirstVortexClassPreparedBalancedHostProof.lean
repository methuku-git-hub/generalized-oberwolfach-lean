module

public import Oberwolfach.FirstVortexClassPreparedBalancedHost
public import Oberwolfach.ClassBalancedMatchingConditions
public import Oberwolfach.FirstVortexClassPreparedOrientedGlobal
public import Oberwolfach.FirstVortexPreparedOrientedResidual
public import Oberwolfach.FirstVortexClassOrientedHostResidual
public import Oberwolfach.FirstVortexPreparedOutcomeResidual

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexClassPreparedBalancedHostProofFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_class_prepared_balanced_host_completion
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P Sclass:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (Dv mm d m:ℕ) (β ε:ℝ)
    (Vort:Vortex U P Dv β ε mm) (F:U→SimpleGraph (Fin n))
    (hF:∀w,(F w).IsRegularOfDegree 2) (θ lam eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ βfinal:ℝ)
    (weight:(Fin (m+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (σE:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) false) t)
    (hρ₀:0<ρ₀) (hb:0≤bmatch) (hbsmall:bmatch≤((ρ₀/4)/40000)/16) (hαb:(2*α)/16≤bmatch)
    (hθδ:10*θ≤δglobal) (hεδ:ε≤δglobal) (hβ:0<βfinal) (hβ1:βfinal≤1)
    (hδ:0<δglobal) (hδbound:δglobal≤(βfinal/100)^2)
    (hSP:Sclass≤P) (hn:0<n) (hnβ:100/βfinal≤(n:ℝ)) (hnδ:2/Real.sqrt δglobal≤(n:ℝ)) (hu:Fintype.card U≤n)
    (hExt:∀Del:SimpleGraph (Fin n),(∀v,(Del.degree v:ℝ)≤Δ*n)→
      ∀u,IsExtendingList (fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σE (Sum.inl e)) x y ∧ ¬Del.Adj x y)
        (rawReservedSpokeList π d (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) u \
          (Vort.extendedVertices 1∪retainedFinalMarkedAt π d
            (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) t Jret u)) βfinal):
    FirstVortexClassPreparedOrientedOutcomeWithGlobalLoad P Sclass π Dv mm d m β ε Vort F hF θ lam eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w σE t Jret →
    FirstVortexClassPreparedOrientedOutcomeWithBalancedHostCompletion P Sclass π Dv mm d m β ε Vort F hF θ lam eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w σE t Jret :=by
  intro hPrep
  unfold FirstVortexClassPreparedOrientedOutcomeWithGlobalLoad at hPrep
  unfold FirstVortexClassPreparedOrientedOutcomeWithBalancedHostCompletion
  have hdec0 : firstVortexClassPreparedGlobalFin n = firstVortexClassPreparedBalancedHostProofFin n := Subsingleton.elim _ _
  have hdec0K : firstVortexClassPreparedGlobalFin K = firstVortexClassPreparedBalancedHostProofFin K := Subsingleton.elim _ _
  have hdec1 : firstVortexClassPreparedBalancedHostFin n = firstVortexClassPreparedBalancedHostProofFin n := Subsingleton.elim _ _
  have hdec1K : firstVortexClassPreparedBalancedHostFin K = firstVortexClassPreparedBalancedHostProofFin K := Subsingleton.elim _ _
  try rw [hdec0] at hPrep
  try rw [hdec0K] at hPrep
  try rw [hdec1]
  try rw [hdec1K]
  intro ni hni ℓ raw selected Hret Wm Wo W Rsrc R hub Del δDel hDel hΔ hξ S T e Q q
  obtain ⟨M,hpos,hdisj,hinc,hlow,hup,hsourceCount,hsource⟩:=hPrep Del δDel hDel hΔ hξ
  refine ⟨M,hpos,hdisj,hinc,hlow,hup,hsourceCount,?_⟩
  intro D absorber Reserve X Z habs H A Used P₀ Sel Kbad
  obtain ⟨hU,hsource'⟩:=hsource D absorber Reserve X Z habs
  intro Mhost hphysical hcorrect
  refine ⟨hU,?_⟩
  have hKbad:Kbad≤Sclass:=by
    dsimp only [Kbad]
    exact long_required_physical_graph_le_host Sclass P₀ Sel π d A D (fun x y=>Used.Adj x y)
      (by intro x y hh;exact hh.1)
  have hcorrect' := hcorrect
  have hdec6 : firstVortexClassPreparedBalancedHostFin 6 = instDecidableEqFin 6 := Subsingleton.elim _ _
  rw [hdec6] at hcorrect'
  have hconditions:=class_balanced_matching_conditions P Sclass Kbad Del π d σE Mhost hSP hKbad hphysical hcorrect'
  have hcont:=first_vortex_class_oriented_host_residual_continuation P Sclass Del π d m ℓ σE t Jret F H A Kbad Used absorber (fun x y=>Mhost x y=1)
    δlocal ρ₀ θ ε lam (2*α) bmatch βfinal δglobal hρ₀ hb hbsmall hαb hθδ hεδ hβ hβ1 hδ hδbound hn hnβ hnδ hu hU hconditions.1 hconditions.2.1
  have hdecC : firstVortexClassOrientedHostResidualFin n = firstVortexClassPreparedBalancedHostProofFin n := Subsingleton.elim _ _
  have hdecCK : firstVortexClassOrientedHostResidualFin K = firstVortexClassPreparedBalancedHostProofFin K := Subsingleton.elim _ _
  try rw [hdecC] at hcont
  try rw [hdecCK] at hcont
  exact hcont (hExt Del (fun v=>(hDel v).trans hΔ)) (M.map q) hsource'
end Oberwolfach
