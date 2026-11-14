module

public import Oberwolfach.OrdinaryBoundaryRootSets

@[expose] public section
/-! The actual outer roots and their remaining neighborhoods supply all
geometric inputs to the triangle boundary finish after sparse cleanup. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_canonical_boundary_remainder
    (Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (hQF:Disjoint Q F)
    (hNoR:∀v∉X,∀w∉X,¬Q.Adj v w)
    (hNoS:∀v∉X,∀u∉Z,¬H v u)
    (hQbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hQdiv:∀u,3∣(Finset.univ.filter (fun v=>H v u)).card)
    (limit:ℝ)
    (C:OrdinaryTriangleSelectedFactors Q F H (ordinaryBoundaryRimSet Q X) (ordinaryBoundaryRowSet H X Z)
      (fun _=>X) (ordinaryBoundaryHubSet H Z X) (ordinary_boundary_root_domains_disjoint Q H X Z) limit):
    ∃R:SimpleGraph V,∃S:V→U→Prop,
      R≤Q ∧ (∀v u,S v u→H v u) ∧ HasOrdinaryWheelDecomposition R S 3 ∧
      let Q':=Q\R;let H':=fun v u=>H v u∧¬S v u;
      Q'≤spanningRestriction Q X ∧ (∀v u,H' v u→H v u∧v∈X∧u∈Z) ∧
      (∀v,Q'.degree v=2*(Finset.univ.filter (H' v)).card) ∧
      (∀u,3∣(Finset.univ.filter (fun v=>H' v u)).card) ∧
      ordinaryHostResources Q' H'⊆ordinaryRootResources X Z ∧
      (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤limit):=by
  let x:=ordinaryOuterRimEmbedding X
  let u:=ordinaryOuterHubEmbedding Z
  let A:=ordinaryBoundaryRimSet Q X
  let B:=ordinaryBoundaryRowSet H X Z
  let Y:=ordinaryBoundaryHubSet H Z X
  have hx:∀i,x i∉X:=fun i=>i.property
  have hu:∀j,u j∉Z:=fun j=>j.property
  have hxcover:∀a∉X,∃i,x i=a:=by intro a ha;exact ⟨⟨a,ha⟩,rfl⟩
  have hucover:∀z∉Z,∃j,u j=z:=by intro z hz;exact ⟨⟨z,hz⟩,rfl⟩
  have hA:∀i,A i⊆X:=fun i=>Finset.inter_subset_right
  have hB:∀i,B i⊆Z:=fun i=>Finset.filter_subset _ _
  have hY:∀j,Y j⊆X:=fun j=>Finset.filter_subset _ _
  have hQr:∀i a,Q.Adj (x i) a↔a∈A i:=by
    intro i a
    simp only [A,ordinaryBoundaryRimSet,Finset.mem_inter,SimpleGraph.mem_neighborFinset]
    constructor
    · intro h;refine ⟨h,?_⟩;by_contra ha;exact hNoR (x i) (hx i) a ha h
    · exact And.left
  have hHr:∀i z,H (x i) z↔z∈B i:=by
    intro i z
    simp only [B,ordinaryBoundaryRowSet,Finset.mem_filter]
    constructor
    · intro h;refine ⟨?_,h⟩;by_contra hz;exact hNoS (x i) (hx i) z hz h
    · exact And.right
  have hHc:∀j a,H a (u j)↔a∈Y j:=by
    intro j a
    simp only [Y,ordinaryBoundaryHubSet,Finset.mem_filter]
    constructor
    · intro h;refine ⟨?_,h⟩;by_contra ha;exact hNoS a ha (u j) (hu j) h
    · exact And.right
  have hFroot:∀i,∀a∈A i,¬F.Adj (x i) a:=by
    intro i a ha hf
    exact (disjoint_iff_inf_le.mp hQF) (v:=x i) (w:=a) ⟨(hQr i a).mpr ha,hf⟩
  exact ordinary_triangle_selected_factors_next_level Q F H X Z x u hx hu hxcover hucover A B (fun _=>X) Y
    hA hB hY hQr hHr hHc hFroot (ordinary_boundary_root_domains_disjoint Q H X Z) limit C hQbal hQdiv
end Oberwolfach
