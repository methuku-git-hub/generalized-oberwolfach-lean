module

public import Oberwolfach.OrdinaryRootFirstFinishData
public import Oberwolfach.OrdinaryRootFirstCleanupFacts
public import Oberwolfach.OrdinaryRootFirstPackingSubhost
public import Oberwolfach.OrdinaryInnerFactorSurvival
public import Oberwolfach.OrdinaryBoundaryChangeFromPacking
public import Oberwolfach.BoundaryDegreeAfterPacking

@[expose] public section
/-! The same retained reserve controls the cleaned host's actual boundary
and the survival of every inner factor host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_first_cleanup_boundary_facts
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell t ν:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W r η ell) (σ:Sym2 (V⊕U)→Bool)
    (O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W r η ell t ν D σ)
    (p ε:ℝ) (ht:0≤t) (hp:0≤p)
    (hsample:BoundaryReserveSupportGood (ordinaryBoundaryGraph (Q\D.rim)
      (fun v u=>H v u∧¬D.spokes v u) X Z) p ε σ):
    let K:=O.context;
    let Q₀:=Q\K.cover.rim;let H₀:=fun v u=>H v u∧¬K.cover.spokes v u;
    let R:=ordinaryRootFirstPackingRim Q F H X T Z W r η ell t K;
    let S:=ordinaryRootFirstPackingSpokes Q F H X T Z W r η ell t K;
    let C:=ordinaryPhysicalGraph R S;
    let Cclean:=ordinaryPhysicalGraph (wheelFamilyRim O.cleanup.wheels) (wheelFamilySpokes O.cleanup.wheels);
    let Q₂:=ordinaryRootFirstCleanRemainderRim Q F H X T Z W r η ell t ν D σ O;
    let H₂:=ordinaryRootFirstCleanRemainderSpokes Q F H X T Z W r η ell t ν D σ O;
    ordinaryPhysicalGraph Q₂ H₂=(ordinaryPhysicalGraph Q₀ H₀\C)\Cclean ∧
    ordinaryBoundaryGraph Q₂ H₂ X Z=(ordinaryBoundaryGraph Q₀ H₀ X Z\C)\Cclean ∧
    Disjoint C (spanningRestriction (ordinaryPhysicalGraph Q₀ H₀) (ordinaryInnerVertices X Z)) ∧
    Disjoint C (retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ) ∧
    (∀w,(((ordinaryBoundaryGraph Q₀ H₀ X Z\retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ)\C).degree w:ℝ)+
      (Cclean.degree w:ℝ)≤t+ν) ∧
    (∀w,((ordinaryBoundaryGraph Q₂ H₂ X Z).degree w:ℝ)≤(p+ε)*Fintype.card (V⊕U)+(t+ν)):=by
  intro K Q₀ H₀ R S C Cclean Q₂ H₂
  have hr:K.reserve=retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ:=by
    change O.context.reserve=retainedGraph (ordinaryBoundaryGraph (Q\O.context.cover.rim)
      (fun v u=>H v u∧¬O.context.cover.spokes v u) X Z) σ
    rw [O.cover_eq]
    exact O.reserve_eq
  have hs:=ordinary_root_first_packing_subhost Q F H X T Z W r η ell t K
  have hf:=ordinary_root_first_cleanup_facts Q F H X T Z W r η ell t K ht σ hr
  have hpre:ordinaryPhysicalGraph (Q₀\R) (fun v u=>H₀ v u∧¬S v u)=ordinaryPhysicalGraph Q₀ H₀\C:=by
    convert hf.1 using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hpost:ordinaryPhysicalGraph Q₂ H₂=(ordinaryPhysicalGraph Q₀ H₀\C)\Cclean:=by
    calc
      _ = (ordinaryPhysicalGraph (Q₀\R) (fun v u=>H₀ v u∧¬S v u))\Cclean :=
        ordinary_physical_graph_typed_deletion (Q₀\R) (wheelFamilyRim O.cleanup.wheels)
          (fun v u=>H₀ v u∧¬S v u) (wheelFamilySpokes O.cleanup.wheels)
      _ = _ := congrArg (fun G:SimpleGraph (V⊕U)=>G\Cclean) hpre
  have hb:=ordinary_boundary_after_physical_packings Q₀ Q₂ H₀ H₂ X Z C Cclean hpost
  have hcr:Disjoint C (retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ):=by
    rw [←hr]
    exact hs.2.2
  have hchanges:=ordinary_boundary_change_degree_after_packings Q₀ H₀ X Z C Cclean σ t ν hf.2 O.cleanup.degree
  have hsample':BoundaryReserveSupportGood (ordinaryBoundaryGraph Q₀ H₀ X Z) p ε σ:=by
    change BoundaryReserveSupportGood (ordinaryBoundaryGraph (Q\O.context.cover.rim)
      (fun v u=>H v u∧¬O.context.cover.spokes v u) X Z) p ε σ
    rw [O.cover_eq]
    exact hsample
  have hbd:=boundary_degree_after_packing (ordinaryBoundaryGraph Q₀ H₀ X Z) C Cclean σ p ε (t+ν)
    hp hsample' hcr hchanges
  refine ⟨hpost,hb,hs.2.1,hcr,hchanges,?_⟩
  intro w
  have hh:=hbd w
  have he:=congrArg (fun G:SimpleGraph (V⊕U)=>(G.degree w:ℝ)) hb
  apply le_trans ?_ hh
  convert le_of_eq he using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
