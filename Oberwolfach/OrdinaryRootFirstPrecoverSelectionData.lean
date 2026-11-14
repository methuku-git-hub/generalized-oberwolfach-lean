module

public import Oberwolfach.OrdinaryRootFirstPrecoverPrior
public import Oberwolfach.OrdinaryRootFirstFinishData
public import Oberwolfach.GraphPrecoverPriorCommutation
public import Oberwolfach.OrdinaryLocalPostRootControls

@[expose] public section
/-! The original pre-cover boundary and inside-factor host supply the
selection interfaces for the actual root-first cleaned host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_first_precover_selection_data
    (Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell t ν:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W r η ell) (σ:Sym2 (V⊕U)→Bool)
    (O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W r η ell t ν D σ) (ht:0≤t)
    (hbase:ordinaryPhysicalGraph Qfactor Hfactor≤spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z)):
    let K:=O.context;
    let G:=ordinaryBoundaryGraph Q H X Z;let R:=retainedGraph G σ;
    let C:=ordinaryRootFirstPrecoverPrior Q F H X T Z W r η ell t K σ;
    let E:=ordinaryPhysicalGraph K.cover.rim K.cover.spokes;
    let J:=ordinaryPhysicalGraph (wheelFamilyRim O.cleanup.wheels) (wheelFamilySpokes O.cleanup.wheels);
    let Klocal:=J⊔spanningRestriction E (ordinaryInnerVertices X Z);
    let Q₂:=ordinaryRootFirstCleanRemainderRim Q F H X T Z W r η ell t ν D σ O;
    let H₂:=ordinaryRootFirstCleanRemainderSpokes Q F H X T Z W r η ell t ν D σ O;
    Disjoint C R ∧
    ordinaryBoundaryGraph Q₂ H₂ X Z=(G\C)\(J⊔E) ∧
    ordinaryBoundaryGraph Q₂ H₂ X Z≤(G\C)\J ∧
    (∀w,(((G\R)\C).degree w:ℝ)+(J.degree w:ℝ)≤t+ν) ∧
    (∀w∉ordinaryInnerVertices X Z,(((G\R)\C).degree w:ℝ)+((J⊔E).degree w:ℝ)≤t+ν+ell) ∧
    (∀w,(Klocal.degree w:ℝ)≤ν+η) ∧
    ordinaryPhysicalGraph Qfactor Hfactor\Klocal≤ordinaryPhysicalGraph Q₂ H₂:=by
  intro K G R C E J Klocal Q₂ H₂
  let B:=ordinaryPhysicalGraph (ordinaryRootFirstPackingRim Q F H X T Z W r η ell t K)
    (ordinaryRootFirstPackingSpokes Q F H X T Z W r η ell t K)
  let Q₀:=Q\K.cover.rim
  let H₀:=fun v u=>H v u∧¬K.cover.spokes v u
  have hreserve:K.reserve=retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ:=by
    change O.context.reserve=retainedGraph (ordinaryBoundaryGraph (Q\O.context.cover.rim)
      (fun v u=>H v u∧¬O.context.cover.spokes v u) X Z) σ
    rw [O.cover_eq];exact O.reserve_eq
  have hprior:=ordinary_root_first_precover_prior Q F H X T Z W r η ell t K ht σ hreserve
  have hf:=ordinary_root_first_cleanup_facts Q F H X T Z W r η ell t K ht σ hreserve
  have hpre:ordinaryPhysicalGraph (Q₀\ordinaryRootFirstPackingRim Q F H X T Z W r η ell t K)
      (fun v u=>H₀ v u∧¬ordinaryRootFirstPackingSpokes Q F H X T Z W r η ell t K v u)=
      ordinaryPhysicalGraph Q₀ H₀\B:=by
    convert hf.1 using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hfinal:ordinaryPhysicalGraph Q₂ H₂=((ordinaryPhysicalGraph Q H\E)\B)\J:=by
    calc
      _ = (ordinaryPhysicalGraph (Q₀\ordinaryRootFirstPackingRim Q F H X T Z W r η ell t K)
        (fun v u=>H₀ v u∧¬ordinaryRootFirstPackingSpokes Q F H X T Z W r η ell t K v u))\J :=
        ordinary_physical_graph_typed_deletion _ _ _ _
      _ = (ordinaryPhysicalGraph Q₀ H₀\B)\J := congrArg (fun G:SimpleGraph (V⊕U)=>G\J) hpre
      _ = _ := by rw [show ordinaryPhysicalGraph Q₀ H₀=ordinaryPhysicalGraph Q H\E from
        ordinary_physical_graph_typed_deletion Q K.cover.rim H K.cover.spokes]
  have hpost:ordinaryPhysicalGraph Q₂ H₂=((ordinaryPhysicalGraph Q H\C)\J)\E:=by
    rw [hfinal]
    dsimp [C,ordinaryRootFirstPrecoverPrior,B,E,G,R]
    ext a b
    simp only [SimpleGraph.sdiff_adj,SimpleGraph.sup_adj,SimpleGraph.inf_adj]
    tauto
  have hpost':ordinaryPhysicalGraph Q₂ H₂=(ordinaryPhysicalGraph Q H\C)\(J⊔E):=by
    rw [hpost]
    ext a b;simp only [SimpleGraph.sdiff_adj,SimpleGraph.sup_adj];tauto
  have hb:=ordinary_boundary_after_physical_packings Q Q₂ H H₂ X Z C (J⊔E) hpost'
  have hsupport:ordinaryBoundaryGraph Q₂ H₂ X Z≤(G\C)\J:=by
    rw [hb]
    intro a b hab
    exact ⟨hab.1,fun hj=>hab.2 (Or.inl hj)⟩
  have hL:∀w,(((G\R)\C).degree w:ℝ)+(J.degree w:ℝ)≤t+ν:=by
    intro w
    have ha:=hprior.2.2 w
    have hb:=O.cleanup.degree w
    linarith only [ha,hb]
  have hout:=ordinary_local_root_cover_class_bounds G C J E R (ordinaryInnerVertices X Z) (t+ν) ell hL K.cover.outside_degree
  have hK:∀w,(Klocal.degree w:ℝ)≤ν+η:=by
    intro w
    have hh:=graph_degree_sup_le J (spanningRestriction E (ordinaryInnerVertices X Z)) w
    have hh':(Klocal.degree w:ℝ)≤(J.degree w:ℝ)+((spanningRestriction E (ordinaryInnerVertices X Z)).degree w:ℝ):=by
      exact_mod_cast hh
    linarith only [hh',O.cleanup.degree w,K.cover.inner_degree w]
  have hkeep:=ordinary_factor_survives_local_root_cover (ordinaryPhysicalGraph Q H)
    (ordinaryPhysicalGraph Qfactor Hfactor) C J E (ordinaryPhysicalGraph Q₂ H₂) X Z hbase hprior.2.1 hpost
  exact ⟨hprior.1,hb,hsupport,hL,hout,hK,hkeep⟩
end Oberwolfach
