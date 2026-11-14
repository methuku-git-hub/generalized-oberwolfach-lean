module

public import Oberwolfach.OrdinaryPairingHubWheelsWithDisjoint
public import Oberwolfach.EndpointBoundaryCompletion

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

theorem ordinary_pairing_endpoint_wheel_families_with_disjoint
    (m:ℕ) (hm:3≤m) (Q F:SimpleGraph V) (H:V→U→Prop)
    (X:Finset V) (Z:Finset U) (x:I↪V) (u:J↪U)
    (hx:∀i,x i∉X) (hu:∀j,u j∉Z)
    (A:I→Finset V) (B:I→Finset U) (T Y:J→Finset V)
    (hA:∀i,A i⊆X) (hB:∀i,B i⊆Z) (hY:∀j,Y j⊆X)
    (hQr:∀i v,Q.Adj (x i) v↔v∈A i) (hHr:∀i z,H (x i) z↔z∈B i)
    (hHc:∀j v,H v (u j)↔v∈Y j) (hFroot:∀i,∀v∈A i,¬F.Adj (x i) v)
    (Kcap Dmax:ℕ) (hKcap:0<Kcap) (hBsize:∀i,(B i).card≤Dmax) (hYsize:∀j,(Y j).card≤Dmax)
    (hmemA:∀v,(Finset.univ.filter (fun i=>v∈A i)).card≤Dmax)
    (hmemB:∀z,(Finset.univ.filter (fun i=>z∈B i)).card≤Dmax)
    (Lconf limit bcount:ℝ) (hLconf:0≤Lconf) (hF:∀v,(F.degree v:ℝ)≤Lconf)
    (hcount:∀i,∀z∈B i,∀v∈X,∀w∈X,
      bcount≤(((X.filter (fun a=>H a z))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
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
      (∀v∉X,∀w,(wheelFamilyRim C).Adj v w↔∃i,v=x i∧w∈A i) ∧
      (∀v∉X,∀z,wheelFamilySpokes C v z↔∃i,v=x i∧z∈B i) ∧
      (∀v,(wheelFamilyRim C).degree v≤2*(Kcap+Dmax)) ∧
      (∀v,(Finset.univ.filter (wheelFamilySpokes C v)).card≤Kcap+Dmax) ∧
      (∀z,(Finset.univ.filter (fun v=>wheelFamilySpokes C v z)).card≤Dmax*(m+1)):=by
  obtain ⟨W,hWdis,hWdec,hWs,hDsupport,hEspoke,hDdeg,hEdeg,hWinner,hhold⟩:=
    ordinary_pairing_hub_wheel_preparation_with_disjoint m Q F H X Z u hu A B T Y hA hB hY
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
    (wheelFamilySpokes W) X x A B hx hA hedge hroot selected.row hrowcross hhold (m+1) Kcap Dmax
    (by omega) hKcap hBsize hmemA hmemB Lconf limit Dmax bcount hLconf hF
    (fun v _=>hDdeg v) hEdeg hcount hbudget
  exact ⟨W,C,hWdis,hCdis,hWdec,hWs,hWinner,hCdec,(fun i=>(hC i).2.2),houtR,houtS,hrim,hrow,hcol⟩
end Oberwolfach
