module

public import Oberwolfach.OrdinaryGeneralFinishTwoPackingsBoundaryDegree
public import Oberwolfach.OrdinaryGeneralSelectionMarginsFromCleanup
public import Oberwolfach.OrdinaryPhysicalInnerRestriction

@[expose] public section
/-! Data on one original/fresh sample sufficient for the conflict-respecting
long-wheel boundary finish after any permitted packing and cleanup. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

structure OrdinaryGeneralFinishSampleInputs
    (m d:ℕ) (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V)
    (X:Finset V) (Z:Finset U) (σ:Sym2 (V⊕U)→Bool)
    (pR pH p density tR tH Ledit βe βh t ν κ ζ ε:ℝ) (Dmax Kcap:ℕ)
    (Lconf:ℝ) (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color):Prop where
  profile:OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH Ledit βe βh s j raw
  good:MixedFreshPairingAvoidingEvent m p (2*p) ζ (spanningRestriction Q X) F
    (ordinaryPhysicalGraph (spanningRestriction Q X) (fun v u=>H v u∧v∈X∧u∈Z))
    (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
    (ordinaryBoundaryHubSet H Z X) (fun i=>(ordinaryBoundaryRimSet Q X i).image Sum.inl)
    (fun i=>(ordinaryBoundaryRowSet H X Z i).image Sum.inr)
    (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val)) σ
  p_pos:0<p
  p_le_one:p≤1
  κ_pos:0<κ
  ζ_pos:0<ζ
  card_hubs:Fintype.card U≤Fintype.card V
  inner_nonempty:X.Nonempty
  κ_scale:κ*Fintype.card V≤βe*Fintype.card (V⊕U)
  support:BoundaryReserveSupportGood (ordinaryBoundaryGraph Q H X Z) p ε σ
  balance:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card
  divisible:∀u,(m+1)∣(Finset.univ.filter (fun v=>H v u)).card
  sample_error:ε≤p^2/4
  leftover_small:t+ν≤(p^2/4)*Fintype.card (V⊕U)
  p_small:p≤4*ζ*min (κ/2) 1
  sqrt_small:20*Real.sqrt (2*p)≤ζ*min (κ/2) 1/2
  cleanup_small:ν≤ζ*min (κ/2) 1*p*Fintype.card (V⊕U)/4
  size_lower:2≤ζ*min (κ/2) 1*p*Fintype.card (V⊕U)/4
  capacity_pos:0<Kcap
  boundary_cap:(2*p)*Fintype.card (V⊕U)≤(Dmax:ℝ)
  conflict_nonneg:0≤Lconf
  conflict_degree:∀v,(F.degree v:ℝ)≤Lconf
  completion:(((Fintype.card (V⊕U)*Dmax*(m+1):ℕ):ℝ)/(Kcap:ℝ)+
    (((m+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*((2*p)*Fintype.card (V⊕U))+2*((Kcap+Dmax:ℕ):ℝ))+
    (Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax < βe*Fintype.card (V⊕U)-3*ν)

def OrdinaryGeneralFinishAfterPackings
    (m:ℕ) (Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (σ:Sym2 (V⊕U)→Bool) (t ν p:ℝ) (Dmax Kcap:ℕ):Prop:=
    let R:=retainedGraph (ordinaryBoundaryGraph Q H X Z) σ;
    ∀(M:OrdinaryUnreservedPackingData Q F H X Z R (m+1) t),
    let C:=ordinaryPackingUsedGraph Q F H X Z R (m+1) t M;
    let Q₁:=ordinaryPackingPostRim Q F H X Z R (m+1) t M;
    let H₁:=ordinaryPackingPostSpokes Q F H X Z R (m+1) t M;
    ∀(K:OrdinaryOutsideCleanupData Q₁ F H₁ X Z C (m+1) ν),
    let Q₂:=ordinaryCleanupPostRim Q₁ F H₁ X Z C (m+1) ν K;
    let H₂:=ordinaryCleanupPostSpokes Q₁ F H₁ X Z C (m+1) ν K;
    OrdinaryGeneralFinishHostResult Q₂ F H₂ X Z m Kcap Dmax (2*p)

theorem ordinary_general_finish_from_sample_inputs
    (m d:ℕ) (hm:3≤m) (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V)
    (X:Finset V) (Z:Finset U) (σ:Sym2 (V⊕U)→Bool)
    (pR pH p density tR tH Ledit βe βh t ν κ ζ ε:ℝ) (Dmax Kcap:ℕ)
    (Lconf:ℝ) (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (data:OrdinaryGeneralFinishSampleInputs m d P Q F H π X Z σ pR pH p density tR tH Ledit βe βh t ν κ ζ ε Dmax Kcap Lconf s j raw):
    OrdinaryGeneralFinishAfterPackings m Q F H X Z σ t ν p Dmax Kcap:=by
  unfold OrdinaryGeneralFinishAfterPackings
  intro R M C Q₁ H₁ K Q₂ H₂
  have hnum:=ordinary_general_selection_margins_from_cleanup P Q F H π d X Z pR pH density tR tH Ledit βe βh
    κ ζ p ε t ν s j raw data.profile data.inner_nonempty data.κ_scale data.κ_pos data.ζ_pos data.p_pos
    data.p_le_one data.card_hubs data.sample_error data.leftover_small data.p_small data.sqrt_small data.cleanup_small data.size_lower
  have hbase:ordinaryPhysicalGraph (spanningRestriction Q X) (fun v u=>H v u∧v∈X∧u∈Z)≤
      spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z):=by
    rw [ordinary_physical_inner_restriction]
  exact ordinary_general_finish_after_two_packings_boundary_degree m hm P Q (spanningRestriction Q X) F H
    (fun v u=>H v u∧v∈X∧u∈Z) π d X Z σ pR pH p density tR tH Ledit βe βh t ν (2*p) ζ ε s j raw
    data.profile data.good data.p_pos.le data.support hbase data.profile.forbidden_disjoint data.balance data.divisible
    hnum.1 hnum.2.1 hnum.2.2.1 hnum.2.2.2.1 hnum.2.2.2.2.1 hnum.2.2.2.2.2
    Dmax Kcap data.capacity_pos data.boundary_cap Lconf data.conflict_nonneg data.conflict_degree data.completion M K
end Oberwolfach
