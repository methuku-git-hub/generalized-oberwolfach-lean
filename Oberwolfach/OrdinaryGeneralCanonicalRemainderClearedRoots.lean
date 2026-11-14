module

public import Oberwolfach.OrdinaryBoundaryRootSets
public import Oberwolfach.OrdinaryPairingBoundaryCompletionClearedRoots
public import Oberwolfach.OrdinaryRootClearedBoundaryClasses
public import Oberwolfach.OrdinaryDeepFreeExtensions
public import Oberwolfach.OrdinaryRootStarBoundaryZero
public import Oberwolfach.OrdinaryBoundaryRemainderLevel

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

theorem ordinary_general_canonical_boundary_remainder_cleared_roots
    (m:ℕ) (hm:3≤m)
    (Q F:SimpleGraph V) (H:V→U→Prop) (X Tdeep:Finset V) (Z Wdeep:Finset U)
    (hTX:Tdeep⊆X) (hWZ:Wdeep⊆Z)
    (hQF:Disjoint Q F)
    (hRootR:∀v∈Tdeep,∀w∉X,¬Q.Adj v w)
    (hRootS:∀v∈Tdeep,∀u∉Z,¬H v u)
    (hRootH:∀u∈Wdeep,∀v∉X,¬H v u)
    (hNoR:∀v∉X,∀w∉X,¬Q.Adj v w)
    (hNoS:∀v∉X,∀u∉Z,¬H v u)
    (hQbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hQdiv:∀u,(m+1)∣(Finset.univ.filter (fun v=>H v u)).card)
    (T:{u:U // u∉Z}→Finset V)
    (Kcap Dmax:ℕ) (hKcap:0<Kcap)
    (hBsize:∀i,(ordinaryBoundaryRowSet H X Z i).card≤Dmax)
    (hYsize:∀j,(ordinaryBoundaryHubSet H Z X j).card≤Dmax)
    (hmemA:∀v,(Finset.univ.filter (fun i=>v∈ordinaryBoundaryRimSet Q X i)).card≤Dmax)
    (hmemB:∀z,(Finset.univ.filter (fun i=>z∈ordinaryBoundaryRowSet H X Z i)).card≤Dmax)
    (Lconf limit bcount:ℝ) (hLconf:0≤Lconf) (hF:∀v,(F.degree v:ℝ)≤Lconf)
    (hcount:∀i,∀z∈ordinaryBoundaryRowSet H X Z i,∀v∈X,∀w∈X,
      bcount≤(((X.filter (fun a=>H a z))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hbudget:((Fintype.card (Σi:{v:V // v∉X},ordinaryBoundaryRowSet H X Z i)*(m+1):ℕ):ℝ)/(Kcap:ℝ)+
      (((m+1:ℕ):ℝ)+3)*(Lconf+1)+2*(limit+2*((Kcap+Dmax:ℕ):ℝ))+
      (Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax<bcount-Tdeep.card)
    (C:OrdinaryPairingSelectedFactors m Q F H (ordinaryBoundaryRimSet Q X) (ordinaryBoundaryRowSet H X Z)
      T (ordinaryBoundaryHubSet H Z X) limit):
    ∃R:SimpleGraph V,∃S:V→U→Prop,
      R≤Q ∧ (∀v u,S v u→H v u) ∧
      HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=m+1)) (ordinaryHostResources R S) ∧
      HasOrdinaryWheelDecomposition R S (m+1) ∧
      let Q':=Q\R;let H':=fun v u=>H v u∧¬S v u;
      Q'≤spanningRestriction Q X ∧ (∀v u,H' v u→H v u∧v∈X∧u∈Z) ∧
      (∀v,Q'.degree v=2*(Finset.univ.filter (H' v)).card) ∧
      (∀u,(m+1)∣(Finset.univ.filter (fun v=>H' v u)).card) ∧
      ordinaryHostResources Q' H'⊆ordinaryRootResources X Z ∧
      (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤limit+((3*(Kcap+Dmax)+Dmax*(m+1):ℕ):ℝ)) ∧
      Disjoint (ordinaryPhysicalGraph R S) (ordinaryDeepRootStar Tdeep Wdeep) ∧
      ordinaryBoundaryGraph R S Tdeep Wdeep=⊥:=by
  let x:=ordinaryOuterRimEmbedding X
  let u:=ordinaryOuterHubEmbedding Z
  let A:=ordinaryBoundaryRimSet Q X
  let B:=ordinaryBoundaryRowSet H X Z
  let Y:=ordinaryBoundaryHubSet H Z X
  have hx:∀i,x i∉X:=fun i=>i.property
  have hu:∀j,u j∉Z:=fun j=>j.property
  have hxcover:∀a∉X,∃i,x i=a:=by intro a ha;exact ⟨⟨a,ha⟩,rfl⟩
  have hucover:∀z∉Z,∃j,u j=z:=by intro z hz;exact ⟨⟨z,hz⟩,rfl⟩
  have hc:=ordinary_root_cleared_boundary_classes Q H X Tdeep Z Wdeep hRootR hRootS hRootH
  have hA:∀i,A i⊆X\Tdeep:=hc.1
  have hB:∀i,B i⊆Z\Wdeep:=hc.2.1
  have hY:∀j,Y j⊆X\Tdeep:=hc.2.2
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
  have hcountfree:∀i,∀z∈B i,∀v∈X\Tdeep,∀w∈X\Tdeep,
      bcount-Tdeep.card≤((((X\Tdeep).filter (fun a=>H a z))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ):=by
    intro i z hz v hv w hw
    have hh:=ordinary_deep_free_extension_count Q H X Tdeep z v w
    have hc:=hcount i z hz v (Finset.mem_sdiff.mp hv).1 w (Finset.mem_sdiff.mp hw).1
    linarith only [hh,hc]
  obtain ⟨R,S,hR,hS,hhost,hdec,hRsupport,hSsupport,hcost,hstar⟩:=ordinary_pairing_boundary_completion_cleared_roots
    m hm Q F H X Tdeep Z Wdeep x u hTX hWZ hx hu hxcover hucover A B T Y hA hB hY hQr hHr hHc hFroot
    Kcap Dmax hKcap hBsize hYsize hmemA hmemB Lconf limit (bcount-Tdeep.card) hLconf hF hcountfree hbudget C
  have hh:=ordinary_boundary_decomposition_remainder_level Q R H S (m+1) X Z
    (limit+((3*(Kcap+Dmax)+Dmax*(m+1):ℕ):ℝ)) hR hS hdec hQbal hQdiv hRsupport hSsupport hcost
  have hzero:=ordinary_root_star_avoided_boundary_empty R S Tdeep Wdeep hstar
  rcases hh with ⟨hsub,hsp,hbal,hdiv,hroot,hinner⟩
  exact ⟨R,S,hR,hS,hhost,hdec,hsub,hsp,hbal,hdiv,hroot,hinner,hstar,hzero⟩
end Oberwolfach
