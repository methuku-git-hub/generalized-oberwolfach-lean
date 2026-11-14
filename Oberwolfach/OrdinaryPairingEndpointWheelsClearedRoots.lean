module

public import Oberwolfach.OrdinaryPairingHubWheelsWithDisjoint
public import Oberwolfach.EndpointBoundaryCompletion
public import Oberwolfach.OrdinaryDeepRootFreeFamilies

@[expose] public section
/-! Complete the selected endpoint pairings to longer ordinary wheels,
    avoiding the actual hub-wheel family and covering every boundary class. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I J:Type} [Fintype V] [Fintype U] [Fintype I] [Fintype J]
  [DecidableEq V] [DecidableEq U] [DecidableEq I] [DecidableEq J]

theorem ordinary_pairing_endpoint_wheel_families_cleared_roots
    (m:ℕ) (hm:3≤m) (Q F:SimpleGraph V) (H:V→U→Prop)
    (X Tdeep:Finset V) (Z Wdeep:Finset U) (x:I↪V) (u:J↪U)
    (hTX:Tdeep⊆X) (hWZ:Wdeep⊆Z)
    (hx:∀i,x i∉X) (hu:∀j,u j∉Z)
    (A:I→Finset V) (B:I→Finset U) (T Y:J→Finset V)
    (hA:∀i,A i⊆X\Tdeep) (hB:∀i,B i⊆Z\Wdeep) (hY:∀j,Y j⊆X\Tdeep)
    (hQr:∀i v,Q.Adj (x i) v↔v∈A i) (hHr:∀i z,H (x i) z↔z∈B i)
    (hHc:∀j v,H v (u j)↔v∈Y j) (hFroot:∀i,∀v∈A i,¬F.Adj (x i) v)
    (Kcap Dmax:ℕ) (hKcap:0<Kcap) (hBsize:∀i,(B i).card≤Dmax) (hYsize:∀j,(Y j).card≤Dmax)
    (hmemA:∀v,(Finset.univ.filter (fun i=>v∈A i)).card≤Dmax)
    (hmemB:∀z,(Finset.univ.filter (fun i=>z∈B i)).card≤Dmax)
    (Lconf limit bcount:ℝ) (hLconf:0≤Lconf) (hF:∀v,(F.degree v:ℝ)≤Lconf)
    (hcount:∀i,∀z∈B i,∀v∈X\Tdeep,∀w∈X\Tdeep,
      bcount≤((((X\Tdeep).filter (fun a=>H a z))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hbudget:((Fintype.card (Σi,B i)*(m+1):ℕ):ℝ)/(Kcap:ℝ)+(((m+1:ℕ):ℝ)+3)*(Lconf+1)+
      2*(limit+2*((Kcap+Dmax:ℕ):ℝ))+(Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax<bcount)
    (selected:OrdinaryPairingSelectedFactors m Q F H A B T Y limit):
    ∃(W:(Σj,selected.hub j)→OrdinaryWheel Q F H (m+1))
      (C:(Σi,B i)→OrdinaryWheel Q F H (m+1)),
      (∀a b,a≠b→Disjoint (ordinaryWheelResources (W a)) (ordinaryWheelResources (W b))) ∧
      (∀a b,a≠b→Disjoint (ordinaryWheelResources (C a)) (ordinaryWheelResources (C b))) ∧
      HasOrdinaryWheelDecomposition (wheelFamilyRim W) (wheelFamilySpokes W) (m+1) ∧
      (∀v z,wheelFamilySpokes W v z↔∃j,u j=z∧v∈Y j) ∧
      (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph (wheelFamilyRim W) (wheelFamilySpokes W))
        (ordinaryInnerVertices X Z)).degree w:ℝ)≤limit) ∧
      HasOrdinaryWheelDecomposition (wheelFamilyRim C) (wheelFamilySpokes C) (m+1) ∧
      (∀i,Disjoint (ordinaryWheelResources (C i)) (ordinaryHostResources (wheelFamilyRim W) (wheelFamilySpokes W))) ∧
      Disjoint (ordinaryPhysicalGraph (wheelFamilyRim W) (wheelFamilySpokes W)) (ordinaryDeepRootStar Tdeep Wdeep) ∧
      Disjoint (ordinaryPhysicalGraph (wheelFamilyRim C) (wheelFamilySpokes C)) (ordinaryDeepRootStar Tdeep Wdeep) ∧
      (∀v∉X\Tdeep,∀w,(wheelFamilyRim C).Adj v w↔∃i,v=x i∧w∈A i) ∧
      (∀v∉X\Tdeep,∀z,wheelFamilySpokes C v z↔∃i,v=x i∧z∈B i) ∧
      (∀v,(wheelFamilyRim C).degree v≤2*(Kcap+Dmax)) ∧
      (∀v,(Finset.univ.filter (wheelFamilySpokes C v)).card≤Kcap+Dmax) ∧
      (∀z,(Finset.univ.filter (fun v=>wheelFamilySpokes C v z)).card≤Dmax*(m+1)):=by
  obtain ⟨W,hWdis,hWdec,hWs,hDsupport,hEspoke,hDdeg,hEdeg,hWinner,hhold⟩:=
    ordinary_pairing_hub_wheel_preparation_with_disjoint m Q F H X Z u hu A B T Y (fun i=>(hA i).trans Finset.sdiff_subset)
      (fun i=>(hB i).trans Finset.sdiff_subset) (fun j=>(hY j).trans Finset.sdiff_subset)
      (fun j v hv=>(hHc j v).mpr hv) Dmax hYsize limit selected
  have hrowcross:∀i j,i≠j→Disjoint (selected.row i).graph (selected.row j).graph:=by
    intro i j hij
    have hh:=selected.cross (Sum.inr i) (Sum.inr j) (by simpa using hij)
    simpa only [Sum.elim_inr] using hh
  have hedge:∀i,∀v∈A i,Q.Adj (x i) v ∧ ¬(wheelFamilyRim W).Adj (x i) v ∧ ¬F.Adj (x i) v:=by
    intro i v hv
    refine ⟨(hQr i v).mpr hv,?_,hFroot i v hv⟩
    intro hh
    exact hx i (hDsupport (x i) v hh).1
  have hroot:∀i,∀z∈B i,H (x i) z ∧ ¬wheelFamilySpokes W (x i) z:=by
    intro i z hz
    refine ⟨(hHr i z).mpr hz,?_⟩
    intro hh
    exact hx i (hEspoke (x i) z hh).1
  obtain ⟨C,hC,hCdis,hCdec,houtR,houtS,hrim,hrow,hcol⟩:=endpoint_boundary_completion Q (wheelFamilyRim W) F H
    (wheelFamilySpokes W) (X\Tdeep) x A B
    (fun i hi=>hx i (Finset.mem_sdiff.mp hi).1) hA hedge hroot selected.row hrowcross hhold (m+1) Kcap Dmax
    (by omega) hKcap hBsize hmemA hmemB Lconf limit Dmax bcount hLconf hF
    (fun v _=>hDdeg v) hEdeg hcount hbudget
  have hWfree:∀v, v∈(wheelFamilyRim W).support→v∉Tdeep:=by
    intro v hv hvT
    obtain ⟨w,hw⟩:=hv
    obtain ⟨i,hi⟩:=SimpleGraph.iSup_adj.mp hw
    have hvw:v∈(ordinaryWheelRim (W i)).support:=⟨w,hi⟩
    obtain ⟨j,_,hvy⟩:=(hWs v (ordinaryWheelHub (W i))).mp ⟨i,rfl,hvw⟩
    exact (Finset.mem_sdiff.mp (hY j hvy)).2 hvT
  have hWstar:Disjoint (ordinaryPhysicalGraph (wheelFamilyRim W) (wheelFamilySpokes W)) (ordinaryDeepRootStar Tdeep Wdeep):=by
    apply (ordinaryPhysicalGraph_disjoint _ _ _ _).mpr
    constructor
    · apply disjoint_iff_inf_le.mpr
      intro v w hvw
      rcases hvw.2.2 with hv|hw
      · exact hWfree v ⟨w,hvw.1⟩ hv
      · exact hWfree w ⟨v,hvw.1.symm⟩ hw
    · intro v z hh
      obtain ⟨j,hj,hv⟩:=(hWs v z).mp hh.1
      rcases hh.2.2 with hvT|hzW
      · exact (Finset.mem_sdiff.mp (hY j hv)).2 hvT
      · exact hu j (hWZ (hj ▸ hzW))
  have hCstar:Disjoint (ordinaryPhysicalGraph (wheelFamilyRim C) (wheelFamilySpokes C)) (ordinaryDeepRootStar Tdeep Wdeep):=by
    apply ordinary_root_free_wheel_family Q F H (m+1) Tdeep Wdeep C
    · intro i v hv
      rcases (hC i).2.1 v hv with he|he
      · intro hvT
        exact hx i.1 (hTX (he ▸ hvT))
      · exact (Finset.mem_sdiff.mp he).2
    · intro i
      rw [(hC i).1]
      exact (Finset.mem_sdiff.mp (hB i.1 i.2.property)).2
  exact ⟨W,C,hWdis,hCdis,hWdec,hWs,hWinner,hCdec,(fun i=>(hC i).2.2),hWstar,hCstar,houtR,houtS,hrim,hrow,hcol⟩
end Oberwolfach
