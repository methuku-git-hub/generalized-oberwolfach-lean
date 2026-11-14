module

public import Oberwolfach.OrdinaryRootFirstFinishFromPrecoverTests
public import Oberwolfach.OrdinaryRootFirstFinishDataDeep
public import Oberwolfach.OrdinaryRootFirstProtectedFromDeepFinish

@[expose] public section
/-! Finish the actual root-first cleaned host using pairing and support
tests formed from the earlier pre-cover parent on the same coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
set_option synthInstance.maxSize 8192
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_root_first_general_protected_from_precover_tests
    (m:ℕ) (hm:3≤m) (P Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop)
    (π:Equiv.Perm V) (d:ℕ) (X T:Finset V) (Z W:Finset U) (η ell t ν:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W (m+1) η ell) (σ:Sym2 (V⊕U)→Bool)
    (O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W (m+1) η ell t ν D σ)
    (pR pH p density tR tH Ledit βe₀ βh₀ βe βh ρ ζ εsup:ℝ)
    (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (ht:0≤t) (hp:0≤p) (hQF:Disjoint Q F)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,(m+1)∣(Finset.univ.filter (fun v=>H v u)).card)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH Ledit βe₀ βh₀ s j raw)
    (hmE:βe*Fintype.card (V⊕U)+3*max η ell≤βe₀*Fintype.card (V⊕U))
    (hmH:βh*Fintype.card (V⊕U)+2*ell≤βh₀*Fintype.card (V⊕U)):
    let K:=O.context;
    let Q₂:=ordinaryRootFirstCleanRemainderRim Q F H X T Z W (m+1) η ell t ν D σ O;
    let H₂:=ordinaryRootFirstCleanRemainderSpokes Q F H X T Z W (m+1) η ell t ν D σ O;
    BoundaryReserveSupportGood (ordinaryBoundaryGraph Q H X Z) p εsup σ→
    OrdinaryBoundaryExtensionGood (Q\K.cover.rim) (fun v u=>H v u∧¬K.cover.spokes v u) X βe p σ→
    OrdinaryBoundaryHubPairGood (fun v u=>H v u∧¬K.cover.spokes v u) Z βh p σ→
    MixedFreshPairingAvoidingEvent m p ρ ζ Qfactor F (ordinaryPhysicalGraph Qfactor Hfactor)
      (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
      (ordinaryBoundaryHubSet H Z X) (fun i=>(ordinaryBoundaryRimSet Q X i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H X Z i).image Sum.inr)
      (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val)) σ→
    ordinaryPhysicalGraph Qfactor Hfactor≤spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z)→
    (p+εsup)*Fintype.card (V⊕U)+(t+ν)≤ρ*Fintype.card (V⊕U)→
    (p^2+εsup)*Fintype.card (V⊕U)+2*(t+ν)≤ρ^2*Fintype.card (V⊕U)→
    (∀j:{u:U // u∉Z},t+ν+ell≤ζ*(p*(ordinaryBoundaryHubSet H Z X j).card))→
    t+ν+ell≤ζ*(p*Fintype.card (V⊕U))→
    (∀j:{u:U // u∉Z},2*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))+
      2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))):ℝ)+(ν+η)≤ζ*(p*(ordinaryBoundaryHubSet H Z X j).card))→
    2*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))+
      2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))):ℝ)+(ν+η)≤ζ*(p*Fintype.card (V⊕U))→
    ∀(Dmax Kcap:ℕ),0<Kcap→ρ*Fintype.card (V⊕U)≤(Dmax:ℝ)→
    ∀Lconf:ℝ,0≤Lconf→(∀v,(F.degree v:ℝ)≤Lconf)→
    ((Fintype.card (Σi:{v:V // v∉X},ordinaryBoundaryRowSet H₂ X Z i)*(m+1):ℕ):ℝ)/(Kcap:ℝ)+
      (((m+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*(ρ*Fintype.card (V⊕U))+2*((Kcap+Dmax:ℕ):ℝ))+
      (Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax<(p^3*βe/2)*Fintype.card (V⊕U)-3*ν-T.card→
    OrdinaryProtectedHostCoverDownResult Q F H X T Z W (m+1)
      (ν+η+(2*(ρ*Fintype.card (V⊕U))+((3*(Kcap+Dmax)+Dmax*(m+1):ℕ):ℝ)))
      (ν+η+(2*(ρ*Fintype.card (V⊕U))+((3*(Kcap+Dmax)+Dmax*(m+1):ℕ):ℝ))):=by
  intro K Q₂ H₂ hsample hevent hhevent hgood hbase hdeg hpair hscaleY hscaleZ hbudgetY hbudgetZ
    Dmax Kcap hKcap hDmax Lconf hLconf hF hcompletion
  obtain ⟨E⟩:=ordinary_root_first_finish_from_precover_tests m hm P Q Qfactor F H Hfactor π d X T Z W η ell t ν
    D σ O pR pH p density tR tH Ledit βe₀ βh₀ βe βh ρ ζ εsup s j raw ht hp hQF hbal hdiv profile hmE hmH
    hsample hevent hhevent hgood hbase hdeg hpair hscaleY hscaleZ hbudgetY hbudgetZ Dmax Kcap hKcap hDmax
    Lconf hLconf hF hcompletion
  exact ordinary_root_first_protected_from_deep_finish Q F H X T Z W (m+1) η ell t ν D σ O
    (2*(ρ*Fintype.card (V⊕U))+((3*(Kcap+Dmax)+Dmax*(m+1):ℕ):ℝ))
    (ordinary_root_first_finish_data_deep Q F H X T Z W (m+1) η ell t ν D σ O _ E) hbal hdiv
end Oberwolfach
