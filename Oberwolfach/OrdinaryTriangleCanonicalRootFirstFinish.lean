module

public import Oberwolfach.OrdinaryTriangleRootFirstFinishFromFactors
public import Oberwolfach.OrdinaryBoundaryRootSets

@[expose] public section
/-! Canonical boundary classes of the actual cleaned host discharge the
triangle root-finish geometry on the same sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_canonical_root_first_finish
    (Q F:SimpleGraph V) (H:V→U→Prop) (X Tdeep:Finset V) (Z Wdeep:Finset U)
    (η ell t ν:ℝ) (Droot:OrdinaryRootCoverData Q F H X Tdeep Z Wdeep 3 η ell)
    (σ:Sym2 (V⊕U)→Bool) (O:OrdinaryRootFirstCleanupOutcome Q F H X Tdeep Z Wdeep 3 η ell t ν Droot σ)
    (hQF:Disjoint Q F) (T:{u:U // u∉Z}→Finset V) (limit:ℝ):
    let Q₂:=ordinaryRootFirstCleanRemainderRim Q F H X Tdeep Z Wdeep 3 η ell t ν Droot σ O;
    let H₂:=ordinaryRootFirstCleanRemainderSpokes Q F H X Tdeep Z Wdeep 3 η ell t ν Droot σ O;
    ∀C:OrdinaryTriangleSelectedFactors Q₂ F H₂ (ordinaryBoundaryRimSet Q₂ X) (ordinaryBoundaryRowSet H₂ X Z)
      T (ordinaryBoundaryHubSet H₂ Z X) (ordinary_boundary_root_domains_disjoint Q₂ H₂ X Z) limit,
    (∀j,Disjoint ((localOrdinaryFactorGraph (C.hub j)).map (Function.Embedding.inl:V↪V⊕U))
      (ordinaryDeepBlocker Tdeep Wdeep))→
    (∀i,Disjoint (endpointFactorGraph (ordinary_boundary_root_domains_disjoint Q₂ H₂ X Z i) (C.row i))
      (ordinaryDeepBlocker Tdeep Wdeep))→
    Nonempty (OrdinaryRootFirstDeepFinishData Q F H X Tdeep Z Wdeep 3 η ell t ν Droot σ O limit):=by
  intro Q₂ H₂ C hhub hrow
  let x:=ordinaryOuterRimEmbedding X
  let u:=ordinaryOuterHubEmbedding Z
  let A:=ordinaryBoundaryRimSet Q₂ X
  let B:=ordinaryBoundaryRowSet H₂ X Z
  let Y:=ordinaryBoundaryHubSet H₂ Z X
  have hx:∀i,x i∉X:=fun i=>i.property
  have hu:∀j,u j∉Z:=fun j=>j.property
  have hxcover:∀a∉X,∃i,x i=a:=by intro a ha;exact ⟨⟨a,ha⟩,rfl⟩
  have hucover:∀z∉Z,∃j,u j=z:=by intro z hz;exact ⟨⟨z,hz⟩,rfl⟩
  have hA:∀i,A i⊆X:=fun i=>Finset.inter_subset_right
  have hB:∀i,B i⊆Z:=fun i=>Finset.filter_subset _ _
  have hY:∀j,Y j⊆X:=fun j=>Finset.filter_subset _ _
  have hNoR:∀v∉X,∀w∉X,¬Q₂.Adj v w:=O.cleanup.no_outer_rim
  have hNoS:∀v∉X,∀u∉Z,¬H₂ v u:=O.cleanup.no_outer_spoke
  have hQr:∀i a,Q₂.Adj (x i) a↔a∈A i:=by
    intro i a
    simp only [A,ordinaryBoundaryRimSet,Finset.mem_inter,SimpleGraph.mem_neighborFinset]
    constructor
    · intro h;refine ⟨h,?_⟩;by_contra ha;exact hNoR (x i) (hx i) a ha h
    · exact And.left
  have hHr:∀i z,H₂ (x i) z↔z∈B i:=by
    intro i z
    simp only [B,ordinaryBoundaryRowSet,Finset.mem_filter]
    constructor
    · intro h;refine ⟨?_,h⟩;by_contra hz;exact hNoS (x i) (hx i) z hz h
    · exact And.right
  have hHc:∀j a,H₂ a (u j)↔a∈Y j:=by
    intro j a
    simp only [Y,ordinaryBoundaryHubSet,Finset.mem_filter]
    constructor
    · intro h;refine ⟨?_,h⟩;by_contra ha;exact hNoS a ha (u j) (hu j) h
    · exact And.right
  have hQ₂F:Disjoint Q₂ F:=hQF.mono_left (show Q₂≤Q from sdiff_le.trans (sdiff_le.trans sdiff_le))
  have hFroot:∀i,∀a∈A i,¬F.Adj (x i) a:=by
    intro i a ha hf
    exact (disjoint_iff_inf_le.mp hQ₂F) (v:=x i) (w:=a) ⟨(hQr i a).mpr ha,hf⟩
  exact ordinary_triangle_root_first_finish_from_factors Q F H X Tdeep Z Wdeep η ell t ν Droot σ O
    O.context.root_sub O.context.hub_sub x u hx hu hxcover hucover A B T Y hA hB hY
    (ordinary_boundary_root_domains_disjoint Q₂ H₂ X Z) limit hQr hHr hHc hFroot C hhub hrow
end Oberwolfach
