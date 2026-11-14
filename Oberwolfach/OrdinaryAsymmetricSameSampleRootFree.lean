module

public import Oberwolfach.OrdinaryGeneralRootFirstAsymmetricMarginsRootFree
public import Oberwolfach.OrdinaryGeneralRootFreeSampledCoverCleanupSubsetProbability
public import Oberwolfach.FiniteLawIntersectionLower

@[expose] public section
/-! Combine root-free cleanup, the boundary support test, and asymmetric
fresh pairings on one sample, retaining the resulting protected cover-down. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
set_option synthInstance.maxSize 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_asymmetric_same_sample_root_free
    {Γ Color:Type} [Fintype Γ] [Fintype Color]
    (m:ℕ) (hm:3≤m) (P Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop)
    (π:Equiv.Perm V) (d:ℕ) (X T:Finset V) (Z W:Finset U) (η ell t ν:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W (m+1) η ell)
    (pR pH p density tR tH Ledit βe₀ βh₀ βe βh ρ ζh ζe n εsup budget deepBudget δsample:ℝ)
    (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (ht:0≤t) (hp:0≤p) (hQF:Disjoint Q F)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,(m+1)∣(Finset.univ.filter (fun v=>H v u)).card)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH Ledit βe₀ βh₀ s j raw)
    (hmE:βe*Fintype.card (V⊕U)+3*max η ell≤βe₀*Fintype.card (V⊕U))
    (hmH:βh*Fintype.card (V⊕U)+2*ell≤βh₀*Fintype.card (V⊕U))
    (hnum:∀σ (O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W (m+1) η ell t ν D σ),
      BoundaryReserveSupportGood (ordinaryBoundaryGraph Q H X Z) p εsup σ→
      OrdinarySampledCoverDegreeGood (ordinaryPhysicalGraph D.rim D.spokes) p δsample σ→
      OrdinaryGeneralRootFirstAsymmetricMargins m Q Qfactor F H Hfactor X T Z W η ell t ν D σ O
        p ρ ζh ζe n εsup βe budget (p*ell+δsample*Fintype.card (V⊕U)))
    (hdeep:η≤deepBudget)
    (μ:FiniteLaw (Sym2 (V⊕U)→Bool)) (a b c:ℝ)
    (hclean:1-a≤μ.probability (OrdinaryGeneralRootFreeSampledCoverCleanupSample m Q F H X T Z W η ell t ν D p βe βh δsample))
    (hsupport:1-b≤μ.probability (BoundaryReserveSupportGood (ordinaryBoundaryGraph Q H X Z) p εsup))
    (hpair:1-c≤μ.probability (MixedFreshPairingAsymmetricEvent m p ρ ζh ζe n Qfactor F
      (ordinaryPhysicalGraph Qfactor Hfactor) (ordinaryPhysicalGraph F (fun _ _=>False))
      (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet H Z X)
      (fun i=>(ordinaryBoundaryRimSet Q X i).image Sum.inl) (fun i=>(ordinaryBoundaryRowSet H X Z i).image Sum.inr)
      (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val)))):
    1-a-b-c≤μ.probability (fun σ=>
      OrdinaryGeneralRootFreeSampledCoverCleanupSample m Q F H X T Z W η ell t ν D p βe βh δsample σ ∧
      BoundaryReserveSupportGood (ordinaryBoundaryGraph Q H X Z) p εsup σ ∧
      MixedFreshPairingAsymmetricEvent m p ρ ζh ζe n Qfactor F
        (ordinaryPhysicalGraph Qfactor Hfactor) (ordinaryPhysicalGraph F (fun _ _=>False))
        (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet H Z X)
        (fun i=>(ordinaryBoundaryRimSet Q X i).image Sum.inl) (fun i=>(ordinaryBoundaryRowSet H X Z i).image Sum.inr)
        (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val)) σ ∧
      OrdinaryProtectedHostCoverDownResult Q F H X T Z W (m+1) budget deepBudget):=by
  let Clean:=OrdinaryGeneralRootFreeSampledCoverCleanupSample m Q F H X T Z W η ell t ν D p βe βh δsample
  let Support:=BoundaryReserveSupportGood (ordinaryBoundaryGraph Q H X Z) p εsup
  let Pair:=MixedFreshPairingAsymmetricEvent m p ρ ζh ζe n Qfactor F
    (ordinaryPhysicalGraph Qfactor Hfactor) (ordinaryPhysicalGraph F (fun _ _=>False))
    (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet H Z X)
    (fun i=>(ordinaryBoundaryRimSet Q X i).image Sum.inl) (fun i=>(ordinaryBoundaryRowSet H X Z i).image Sum.inr)
    (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val))
  have hcs:=finiteLaw_intersection_lower μ Clean Support a b hclean hsupport
  have hall:=finiteLaw_intersection_lower μ (fun σ=>Clean σ∧Support σ) Pair (a+b) c (by linarith only [hcs]) hpair
  have hall':1-a-b-c≤μ.probability (fun σ=>(Clean σ∧Support σ)∧Pair σ):=by linarith only [hall]
  apply hall'.trans
  apply finiteLaw_probability_mono
  intro σ hσ
  obtain ⟨⟨⟨⟨O,hrootfree⟩,hevent,hhevent⟩,hcover⟩,hsup⟩:=hσ.1
  refine ⟨hσ.1.1,hsup,hσ.2,?_⟩
  exact ordinary_general_root_first_protected_of_asymmetric_margins m hm P Q Qfactor F H Hfactor π d X T Z W η ell t ν D σ O hrootfree
    pR pH p density tR tH Ledit βe₀ βh₀ βe βh ρ ζh ζe n εsup budget deepBudget δsample s j raw ht hp hQF hbal hdiv profile hmE hmH
    hsup hevent hhevent hσ.2 hcover (hnum σ O hsup hcover) hdeep
end Oberwolfach
