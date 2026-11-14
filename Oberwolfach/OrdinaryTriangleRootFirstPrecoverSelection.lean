module

public import Oberwolfach.OrdinaryTriangleBoundaryLocalAvoidingSelection
public import Oberwolfach.OrdinaryRootFirstPrecoverSelectionData
public import Oberwolfach.OrdinaryRootFirstCleanupRemainder
public import Oberwolfach.OrdinaryTriangleSelectedFactors

@[expose] public section
/-! The fresh triangle factors can be selected after the root-first cleanup
    while avoiding the same protected deeper block. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_root_first_precover_selected_factors
    (Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop) (X T:Finset V) (Z W:Finset U)
    (η ell t ν:ℝ) (Droot:OrdinaryRootCoverData Q F H X T Z W 3 η ell)
    (σ:Sym2 (V⊕U)→Bool) (O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W 3 η ell t ν Droot σ)
    (p ρ ζ εsup:ℝ) (ht:0≤t) (hp:0≤p)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,3∣(Finset.univ.filter (fun v=>H v u)).card)
    (hgood:MixedFreshBoundaryAvoidingEvent p ρ ζ Qfactor F (ordinaryPhysicalGraph Qfactor Hfactor)
      (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
      (ordinaryBoundaryHubSet H Z X) (fun i=>(ordinaryBoundaryRimSet Q X i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H X Z i).image Sum.inr)
      (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val))
      (ordinary_boundary_root_domains_disjoint Q H X Z) σ)
    (hsample:BoundaryReserveSupportGood (ordinaryBoundaryGraph Q H X Z) p εsup σ)
    (hbase:ordinaryPhysicalGraph Qfactor Hfactor≤spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z))
    (hdeg:(p+εsup)*Fintype.card (V⊕U)+(t+ν)≤ρ*Fintype.card (V⊕U))
    (hpair:(p^2+εsup)*Fintype.card (V⊕U)+2*(t+ν)≤ρ^2*Fintype.card (V⊕U))
    (hscaleY:∀j:{u:U // u∉Z},t+ν+ell≤ζ*(p*(ordinaryBoundaryHubSet H Z X j).card))
    (hscaleZ:∀i:{v:V // v∉X},t+ν+ell≤ζ*(p*(ordinaryBoundaryRowSet H X Z i).card))
    (hbudgetY:∀j:{u:U // u∉Z},2*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))+
      2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))):ℝ)+(ν+η)≤ζ*(p*(ordinaryBoundaryHubSet H Z X j).card))
    (hbudgetZ:∀i:{v:V // v∉X},2*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))+
      2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))):ℝ)+(ν+η)≤ζ*(p*(ordinaryBoundaryRowSet H X Z i).card)):
    let Q₂:=ordinaryRootFirstCleanRemainderRim Q F H X T Z W 3 η ell t ν Droot σ O;
    let H₂:=ordinaryRootFirstCleanRemainderSpokes Q F H X T Z W 3 η ell t ν Droot σ O;
    Nonempty (OrdinaryTriangleSelectedFactors Q₂ F H₂ (ordinaryBoundaryRimSet Q₂ X) (ordinaryBoundaryRowSet H₂ X Z)
      (ordinaryBoundaryHubSet H Z X) (ordinaryBoundaryHubSet H₂ Z X)
      (ordinary_boundary_root_domains_disjoint Q₂ H₂ X Z) (2*(ρ*Fintype.card (V⊕U)))) :=by
  intro Q₂ H₂
  let Kroot:=O.context
  let G:=ordinaryBoundaryGraph Q H X Z
  let C:=ordinaryRootFirstPrecoverPrior Q F H X T Z W 3 η ell t Kroot σ
  let E:=ordinaryPhysicalGraph Kroot.cover.rim Kroot.cover.spokes
  let J:=ordinaryPhysicalGraph (wheelFamilyRim O.cleanup.wheels) (wheelFamilySpokes O.cleanup.wheels)
  let Klocal:=J⊔spanningRestriction E (ordinaryInnerVertices X Z)
  obtain ⟨hCR,hphys,hsupport,hLsupport,hLoutside,hKlocal,hkeep⟩:=
    ordinary_root_first_precover_selection_data Q Qfactor F H Hfactor X T Z W 3 η ell t ν Droot σ O ht hbase
  obtain ⟨_,hbal₂,hdiv₂,hNoR,hNoS,_,_,_⟩:=
    ordinary_root_first_cleanup_remainder Q F H X T Z W 3 η ell t ν Droot σ O hbal hdiv
  have hLhub:∀j:{u:U // u∉Z},((((G\retainedGraph G σ)\C).degree (Sum.inr j.val):ℝ)+
      ((J⊔E).degree (Sum.inr j.val):ℝ)≤t+ν+ell):=by
    intro j
    have hh:=hLoutside (Sum.inr j.val) (by simpa [ordinaryInnerVertices_right] using j.property)
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hLrim:∀i:{v:V // v∉X},((((G\retainedGraph G σ)\C).degree (Sum.inl i.val):ℝ)+
      ((J⊔E).degree (Sum.inl i.val):ℝ)≤t+ν+ell):=by
    intro i
    have hh:=hLoutside (Sum.inl i.val) (by simpa [ordinaryInnerVertices_left] using i.property)
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  obtain ⟨Sel,_,_⟩:=ordinary_triangle_sampled_boundary_selection_local_avoiding
    Q Qfactor Q₂ F H Hfactor H₂ X Z C J (J⊔E) Klocal σ p ρ ζ εsup (t+ν) (t+ν+ell) (ν+η)
    hgood hp hsample hCR hphys hsupport hLsupport
    (by intro j; have hh:=hLhub j; convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro i; have hh:=hLrim i; convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro w; have hh:=hKlocal w; convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hkeep
    hNoR hNoS
    (by intro v; have hh:=hbal₂ v; convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro u; have hh:=hdiv₂ u; convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    hdeg hpair hscaleY hscaleZ hbudgetY hbudgetZ
  exact ⟨Sel⟩
end Oberwolfach
