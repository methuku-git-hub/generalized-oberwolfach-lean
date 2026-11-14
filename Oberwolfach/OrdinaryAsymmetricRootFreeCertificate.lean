module

public import Oberwolfach.OrdinaryAsymmetricSameSampleRootFree
public import Oberwolfach.OrdinaryWheelCertificateFromProbability

@[expose] public section
/-! The asymmetric same-sample cleanup and pairing result is directly
usable as a protected level-chain certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_asymmetric_root_free_certificate
    (m:ℕ) (Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop) (X T:Finset V) (Z W:Finset U)
    (p ρ ζh ζe n εsup τ ν η ell βe βh δsample failure budget deepBudget cost deepCost:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W (m+1) η ell)
    (μ:FiniteLaw (Sym2 (V⊕U)→Bool)) (hn:16≤Fintype.card V) (hfailure:failure≤1/4)
    (hcost:budget≤cost) (hdeep:deepBudget≤deepCost)
    (hprob:1-failure≤μ.probability (fun σ=>
      OrdinaryGeneralRootFreeSampledCoverCleanupSample m Q F H X T Z W η ell τ ν D p βe βh δsample σ ∧
      BoundaryReserveSupportGood (ordinaryBoundaryGraph Q H X Z) p εsup σ ∧
      MixedFreshPairingAsymmetricEvent m p ρ ζh ζe n Qfactor F
        (ordinaryPhysicalGraph Qfactor Hfactor) (ordinaryPhysicalGraph F (fun _ _=>False))
        (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet H Z X)
        (fun i=>(ordinaryBoundaryRimSet Q X i).image Sum.inl) (fun i=>(ordinaryBoundaryRowSet H X Z i).image Sum.inr)
        (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val)) σ ∧
      OrdinaryProtectedHostCoverDownResult Q F H X T Z W (m+1) budget deepBudget)):
    OrdinaryWheelLikelySeparateCostsCertificate Q F H X T Z W (m+1) cost deepCost:=by
  apply ordinary_wheel_certificate_from_probability Q F H X T Z W (m+1) cost deepCost budget deepBudget failure μ
    _ hn hfailure hprob
  · intro σ hσ
    exact hσ.2.2.2
  · exact hcost
  · exact hdeep
end Oberwolfach
