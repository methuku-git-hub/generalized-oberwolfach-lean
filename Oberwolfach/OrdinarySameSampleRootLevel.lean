module

public import Oberwolfach.OrdinaryGeneralFinishAfterRootCoverContext
public import Oberwolfach.OrdinaryLevelFromRootContext
public import Oberwolfach.OrdinaryBoundaryRowSumFromBoundary
public import Oberwolfach.OrdinaryGeneralSampledRemainderLocalCleared
public import Oberwolfach.OrdinaryLocalRootCoverSelectionData
public import Oberwolfach.OrdinaryInnerExtensionsAfterLocalCover
public import Oberwolfach.OrdinaryRootCoverData
public import Oberwolfach.BoundaryDegreeAfterPacking
public import Oberwolfach.OrdinaryGeneralFinishHostRootClearedResult
public import Oberwolfach.OrdinaryInnerCountsAfterPackingCleanup
public import Oberwolfach.OrdinaryCleanupPostFacts
public import Oberwolfach.OrdinaryInnerFactorSurvival
public import Oberwolfach.OrdinaryBoundaryChangeFromPacking
public import Oberwolfach.OrdinaryBoundaryRowSumBound

@[expose] public section
/-! Complete the actual general-length boundary following the unreserved
packing and its sparse cleanup, with the extension counts inherited from the
same boundary sample. Numerical and parent-event inputs remain explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_general_same_sample_root_level
    (m:ℕ) (hm:3≤m)
    (P Q₀ Q F:SimpleGraph V) (H₀ H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
    (X T:Finset V) (Z W:Finset U) (σ:Sym2 (V⊕U)→Bool)
    (hTX:T⊆X) (hWZ:W⊆Z)
    (pR pH p density tR tH Ledit βe βh t ν η ell ρ ζ ε:ℝ)
    (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q₀ F H₀ π d X Z pR pH density tR tH Ledit βe βh s j raw)
    (hgood:MixedFreshPairingAvoidingEvent m p ρ ζ Q F (ordinaryPhysicalGraph Q H)
      (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
      (ordinaryBoundaryHubSet H₀ Z X)
      (fun i=>(ordinaryBoundaryRimSet Q₀ X i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H₀ X Z i).image Sum.inr)
      (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val)) σ)
    (hp:0≤p) (hsample:BoundaryReserveSupportGood (ordinaryBoundaryGraph Q₀ H₀ X Z) p ε σ)
    (hbase:ordinaryPhysicalGraph Q H≤spanningRestriction (ordinaryPhysicalGraph Q₀ H₀) (ordinaryInnerVertices X Z))
    (hQF:Disjoint Q₀ F)
    (hbal:∀v,Q₀.degree v=2*(Finset.univ.filter (H₀ v)).card)
    (hdiv:∀u,(m+1)∣(Finset.univ.filter (fun v=>H₀ v u)).card)
    (hdeg:(p+ε)*Fintype.card (V⊕U)+(t+ν)≤ρ*Fintype.card (V⊕U))
    (hpair:(p^2+ε)*Fintype.card (V⊕U)+2*(t+ν)≤ρ^2*Fintype.card (V⊕U))
    (hscaleY:∀j:{u:U // u∉Z},t+ν+ell≤ζ*(p*(ordinaryBoundaryHubSet H₀ Z X j).card))
    (hscaleZ:t+ν+ell≤ζ*(p*Fintype.card (V⊕U)))
    (hbudgetY:∀j:{u:U // u∉Z},2*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))+
      2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))) :ℝ)+(ν+η)≤ζ*(p*(ordinaryBoundaryHubSet H₀ Z X j).card))
    (hbudgetZ:2*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))+
      2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))) :ℝ)+(ν+η)≤ζ*(p*Fintype.card (V⊕U)))
    (Dmax Kcap:ℕ) (hKcap:0<Kcap)
    (hDmax:ρ*Fintype.card (V⊕U)≤(Dmax:ℝ))
    (Lconf:ℝ) (hLconf:0≤Lconf) (hF:∀v,(F.degree v:ℝ)≤Lconf)
    (hcompletion:(((Fintype.card (V⊕U)*Dmax*(m+1):ℕ):ℝ)/(Kcap:ℝ)+
      (((m+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*(ρ*Fintype.card (V⊕U))+2*((Kcap+Dmax:ℕ):ℝ))+
      (Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax < βe*Fintype.card (V⊕U)-3*ν-3*η-T.card)):
    ∀(ctx:OrdinaryPackingCleanupRootContext Q₀ F H₀ X T Z W
      (retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ) (m+1) t ν η ell),
    Disjoint (ordinaryPhysicalGraph (wheelFamilyRim ctx.cleanup.wheels) (wheelFamilySpokes ctx.cleanup.wheels))
      (ordinaryDeepBlocker T W) →
    OrdinaryGeneralRootLevelResult Q₀ F H₀ X T Z W m Kcap Dmax ν η ρ:=by
  intro ctx hcleanup
  have hf:=ordinary_general_finish_after_root_cover_context m hm P Q₀ Q F H₀ H π d X T Z W σ hTX hWZ
    pR pH p density tR tH Ledit βe βh t ν η ell ρ ζ ε s j raw profile hgood hp hsample hbase hQF hbal hdiv
    hdeg hpair hscaleY hscaleZ hbudgetY hbudgetZ Dmax Kcap hKcap hDmax Lconf hLconf hF hcompletion ctx
  exact ordinary_level_from_root_context Q₀ F H₀ X T Z W (retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ)
    m Kcap Dmax t ν η ell ρ hTX hWZ hbal hdiv ctx hcleanup hf
end Oberwolfach
