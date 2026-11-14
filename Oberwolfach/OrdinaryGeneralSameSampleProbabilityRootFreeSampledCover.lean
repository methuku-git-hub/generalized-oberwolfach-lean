module

public import Oberwolfach.OrdinaryGeneralSameSampleProbability
public import Oberwolfach.OrdinaryGeneralRootFirstSampledCoverMarginsRootFree
public import Oberwolfach.OrdinaryGeneralRootFreeSampledCoverCleanupSubsetProbability

@[expose] public section
/-! The same cleanup and pairing sample admits separate total and deep
boundary budgets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_general_same_sample_probability_root_free_sampled_cover
    {Γ Color:Type} [Fintype Γ] [Fintype Color]
    (m:ℕ) (hm:3≤m) (P Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop)
    (π:Equiv.Perm V) (d:ℕ) (X T:Finset V) (Z W:Finset U) (η ell t ν:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W (m+1) η ell)
    (pR pH p density tR tH Ledit βe₀ βh₀ βe βh ρ ζ εsup budget deepBudget δsample:ℝ)
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
      OrdinaryGeneralRootFirstSampledCoverMargins m Q Qfactor F H Hfactor X T Z W η ell t ν D σ O p ρ ζ εsup βe budget
        (p*ell+δsample*Fintype.card (V⊕U)))
    (hdeep:η≤deepBudget)
    (μ:FiniteLaw (Sym2 (V⊕U)→Bool)) (a b:ℝ)
    (hclean:1-a≤μ.probability (OrdinaryGeneralRootFreeSampledCoverCleanupSample m Q F H X T Z W η ell t ν D p βe βh δsample))
    (hfresh:1-b≤μ.probability (OrdinaryGeneralFreshPairingSample m Q Qfactor F H Hfactor X Z p ρ ζ εsup)):
    1-a-b≤μ.probability (fun σ=>
      OrdinaryGeneralRootFreeSampledCoverCleanupSample m Q F H X T Z W η ell t ν D p βe βh δsample σ ∧
      OrdinaryGeneralFreshPairingSample m Q Qfactor F H Hfactor X Z p ρ ζ εsup σ ∧
      OrdinaryProtectedHostCoverDownResult Q F H X T Z W (m+1) budget deepBudget) :=by
  let Clean:=OrdinaryGeneralRootFreeSampledCoverCleanupSample m Q F H X T Z W η ell t ν D p βe βh δsample
  let Fresh:=OrdinaryGeneralFreshPairingSample m Q Qfactor F H Hfactor X Z p ρ ζ εsup
  have hi:=finiteLaw_intersection_lower μ Clean Fresh a b hclean hfresh
  apply hi.trans
  apply finiteLaw_probability_mono
  intro σ hσ
  obtain ⟨⟨⟨O,hrootfree⟩,hevent,hhevent⟩,hcover⟩:=hσ.1
  obtain ⟨hsupport,hpair⟩:=hσ.2
  refine ⟨hσ.1,hσ.2,?_⟩
  exact ordinary_general_root_first_protected_of_sampled_cover_margins_root_free m hm P Q Qfactor F H Hfactor π d X T Z W η ell t ν D σ O hrootfree
    pR pH p density tR tH Ledit βe₀ βh₀ βe βh ρ ζ εsup budget deepBudget δsample s j raw ht hp hQF hbal hdiv profile hmE hmH
    hsupport hevent hhevent hpair hcover (hnum σ O hsupport hcover) hdeep
end Oberwolfach
