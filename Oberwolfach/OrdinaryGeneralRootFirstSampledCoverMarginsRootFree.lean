module

public import Oberwolfach.OrdinaryGeneralRootFirstSampledCoverMargins
public import Oberwolfach.OrdinarySampledCoverDegree
public import Oberwolfach.OrdinaryGeneralRootFirstMargins
public import Oberwolfach.OrdinaryRootFirstGeneralProtectedInnerExtensionsRootFreeSampledCover

@[expose] public section
/-! The actual root-star-free finish lets total and deep-boundary budgets
be discharged independently on the same cleaned host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_general_root_first_protected_of_sampled_cover_margins_root_free
    {Γ Color:Type} [Fintype Γ] [Fintype Color]
    (m:ℕ) (hm:3≤m) (P Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop)
    (π:Equiv.Perm V) (d:ℕ) (X T:Finset V) (Z W:Finset U) (η ell t ν:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W (m+1) η ell) (σ:Sym2 (V⊕U)→Bool)
    (O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W (m+1) η ell t ν D σ)
    (hcleanup:Disjoint (ordinaryPhysicalGraph (wheelFamilyRim O.cleanup.wheels)
      (wheelFamilySpokes O.cleanup.wheels)) (ordinaryDeepRootStar T W))
    (pR pH p density tR tH Ledit βe₀ βh₀ βe βh ρ ζ εsup budget deepBudget δsample:ℝ)
    (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (ht:0≤t) (hp:0≤p) (hQF:Disjoint Q F)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,(m+1)∣(Finset.univ.filter (fun v=>H v u)).card)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH Ledit βe₀ βh₀ s j raw)
    (hmE:βe*Fintype.card (V⊕U)+3*max η ell≤βe₀*Fintype.card (V⊕U))
    (hmH:βh*Fintype.card (V⊕U)+2*ell≤βh₀*Fintype.card (V⊕U))
    (hsample:BoundaryReserveSupportGood (ordinaryBoundaryGraph Q H X Z) p εsup σ)
    (hevent:OrdinaryBoundaryExtensionGood (Q\D.rim) (fun v u=>H v u∧¬D.spokes v u) X βe p σ)
    (hhevent:OrdinaryBoundaryHubPairGood (fun v u=>H v u∧¬D.spokes v u) Z βh p σ)
    (hgood:MixedFreshPairingAvoidingEvent m p ρ ζ Qfactor F (ordinaryPhysicalGraph Qfactor Hfactor)
      (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
      (ordinaryBoundaryHubSet H Z X) (fun i=>(ordinaryBoundaryRimSet Q X i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H X Z i).image Sum.inr)
      (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val)) σ)
    (hcover:OrdinarySampledCoverDegreeGood (ordinaryPhysicalGraph D.rim D.spokes) p δsample σ)
    (hnum:OrdinaryGeneralRootFirstSampledCoverMargins m Q Qfactor F H Hfactor X T Z W η ell t ν D σ O p ρ ζ εsup βe budget
      (p*ell+δsample*Fintype.card (V⊕U)))
    (hdeep:η≤deepBudget):
    OrdinaryProtectedHostCoverDownResult Q F H X T Z W (m+1) budget deepBudget :=by
  obtain ⟨hbase,hdeg,hpair,hscaleY,hscaleZ,hbudgetY,hbudgetZ,Dmax,Kcap,hKcap,hDmax,Lconf,hLconf,hF,hcompletion,hbudget⟩:=hnum
  have hevent':OrdinaryBoundaryExtensionGood (Q\O.context.cover.rim)
      (fun v u=>H v u∧¬O.context.cover.spokes v u) X βe p σ:=by
    simpa only [O.cover_eq] using hevent
  have hhevent':OrdinaryBoundaryHubPairGood (fun v u=>H v u∧¬O.context.cover.spokes v u) Z βh p σ:=by
    simpa only [O.cover_eq] using hhevent
  have hh:=ordinary_root_first_general_protected_inner_extensions_root_free_sampled_cover m hm P Q Qfactor F H Hfactor π d X T Z W η ell t ν D σ O hcleanup
    pR pH p density tR tH Ledit βe₀ βh₀ βe βh ρ ζ εsup s j raw ht hp hQF hbal hdiv profile hmE hmH (p*ell+δsample*Fintype.card (V⊕U))
    (ordinary_sampled_cover_boundary_degree Q F H X T Z W (m+1) η ell p δsample D σ hp hcover)
    hsample hevent' hhevent' hgood hbase hdeg hpair hscaleY hscaleZ hbudgetY hbudgetZ
    Dmax Kcap hKcap hDmax Lconf hLconf hF hcompletion
  exact ordinary_protected_cover_down_cost_mono Q F H X T Z W (m+1) _ _ budget deepBudget hbudget hdeep hh
end Oberwolfach
