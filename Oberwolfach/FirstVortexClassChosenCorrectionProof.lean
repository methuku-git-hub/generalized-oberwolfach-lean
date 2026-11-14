module

public import Oberwolfach.FirstVortexClassBalancedAtChosenCorrection

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexClassChosenCorrectionProofFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_class_balanced_at_chosen_correction
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P Sclass:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (Dv mm d m:ℕ) (β ε:ℝ)
    (Vort:Vortex U P Dv β ε mm) (F:U→SimpleGraph (Fin n))
    (hF:∀w,(F w).IsRegularOfDegree 2) (θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ:ℝ)
    (weight:(Fin (m+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (σE:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) false) t)
    (Del:SimpleGraph (Fin n)) (Mhost:Fin n→Fin n→ℕ) (ξPart δcorr:ℝ)
    (hDel:∀v,(Del.degree v:ℝ)≤(ξPart+δcorr)*n)
    (hΔ:ξPart+δcorr≤Δ) (hξ:ξPart+δcorr≤ξ)
    (hphysical:∀x y,Mhost x y+Mhost y x=if Sclass.Adj x y then 1 else 0)
    (hcorrect:orientationDisagreementGraph (longPhysicalStateGraph P σE {0,1,2,3,4})
      (fun e=>(σE (Sum.inl e)).2) Mhost≤Del)
    (hbalance:∀v,(∑w,Mhost v w)=Fintype.card U ∧ (∑w,Mhost w v)=Fintype.card U):
    FirstVortexClassPreparedOrientedOutcomeWithBalancedDegrees P Sclass π Dv mm d m β ε Vort F hF θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w σE t Jret →
    FirstVortexClassBalancedAtChosenCorrection P Sclass π Dv mm d m β ε Vort F hF θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w σE t Jret Del Mhost :=by
  intro hPrep
  unfold FirstVortexClassPreparedOrientedOutcomeWithBalancedDegrees at hPrep
  unfold FirstVortexClassBalancedAtChosenCorrection
  have hdec0 : firstVortexClassPreparedBalancedDegreesFin n = firstVortexClassChosenCorrectionProofFin n := Subsingleton.elim _ _
  have hdec0K : firstVortexClassPreparedBalancedDegreesFin K = firstVortexClassChosenCorrectionProofFin K := Subsingleton.elim _ _
  have hdec1 : firstVortexClassChosenCorrectionFin n = firstVortexClassChosenCorrectionProofFin n := Subsingleton.elim _ _
  have hdec1K : firstVortexClassChosenCorrectionFin K = firstVortexClassChosenCorrectionProofFin K := Subsingleton.elim _ _
  try rw [hdec0] at hPrep
  try rw [hdec0K] at hPrep
  try rw [hdec1]
  try rw [hdec1K]
  have hn:(0:ℝ)≤n:=by positivity
  have hbΔ:(ξPart+δcorr)*n≤Δ*n:=mul_le_mul_of_nonneg_right hΔ hn
  have hbξ:(ξPart+δcorr)*n≤ξ*n:=mul_le_mul_of_nonneg_right hξ hn
  intro ni hni ℓ raw selected Hret Wm Wo W Rsrc R hub S T e Q q
  obtain ⟨M,hpos,hdisj,hinc,hlow,hup,hcount,hsource⟩:=hPrep Del ((ξPart+δcorr)*n) hDel hbΔ hbξ
  refine ⟨M,hpos,hdisj,hinc,hlow,hup,hcount,?_⟩
  intro D absorber Reserve X Z habs H A Used P₀ Sel Kbad
  exact hsource D absorber Reserve X Z habs Mhost hphysical hcorrect hbalance
end Oberwolfach
