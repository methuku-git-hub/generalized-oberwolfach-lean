module

public import Oberwolfach.OrdinarySelectedMatchingFamilyPostDemandResult
public import Oberwolfach.OrdinarySelectedMatchingFamilyPostDemandPlainSpokes

@[expose] public section
/-! Rim deletion leaves every spoke state unchanged. This adapter records
that equality before the large capacity and load arguments are applied. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance 100000] Finset.decidableDforallFinset

theorem ordinary_selected_family_postdemand_plain_spokes
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Cres:∀u,Finset (F u).ConnectedComponent) (i₀:Fin K) (rsv θ lam a γ:ℝ)
    (m d:ℕ) (π:Equiv.Perm (Fin n)) (P Del Target Protect Bad:SimpleGraph (Fin n))
    (Inner:Finset (Fin n)) (bRate:ℝ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (tret:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) tret)
    (h:OrdinarySelectedMatchingFamilyPostDemandResult F hF Cres i₀ rsv θ lam a γ m d π P Del Target Protect Bad Inner bRate σ tret Jret):
    OrdinarySelectedMatchingFamilyPostDemandPlainSpokes F hF Cres i₀ rsv θ lam a γ m d π P Del Target Protect Bad Inner bRate σ tret Jret :=by
  have hs (raw:RawMarkedOutcome (Fin n) U Bool Bool) (D:Finset (Sym2 (Fin n))):
      rawMarkedPairSpokes π d (rawMarkedDeleteRims raw D) true true=rawMarkedPairSpokes π d raw true true:=by
    funext g v u
    rfl
  unfold OrdinarySelectedMatchingFamilyPostDemandResult at h
  unfold OrdinarySelectedMatchingFamilyPostDemandPlainSpokes
  dsimp only at h ⊢
  simp only [rawMarkedPairSpokes,rawMarkedDeleteRims] at h ⊢
  exact h
end Oberwolfach
