module

public import Oberwolfach.OrdinaryPairingEndpointWheelsAvoidingDeep
public import Oberwolfach.OrdinaryCombineBoundaryWheelFamiliesAvoiding

@[expose] public section
/-! Complete the selected general-length factors and pairings to a single
    boundary wheel decomposition with an explicit inner physical-degree cost. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I J:Type} [Fintype V] [Fintype U] [Fintype I] [Fintype J]
  [DecidableEq V] [DecidableEq U] [DecidableEq I] [DecidableEq J]

theorem ordinary_pairing_boundary_completion_avoiding_deep
    (m:ℕ) (hm:3≤m) (Q F:SimpleGraph V) (H:V→U→Prop)
    (X Tdeep:Finset V) (Z Wdeep:Finset U) (x:I↪V) (u:J↪U)
    (hTX:Tdeep⊆X) (hWZ:Wdeep⊆Z)
    (hx:∀i,x i∉X) (hu:∀j,u j∉Z)
    (hxcover:∀v∉X,∃i,x i=v) (hucover:∀z∉Z,∃j,u j=z)
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
      2*(limit+Tdeep.card+2*((Kcap+Dmax:ℕ):ℝ))+((Dmax:ℝ)+Tdeep.card)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax<bcount)
    (selected:OrdinaryPairingSelectedFactorsAvoiding m Q F H A B T Y limit (ordinaryDeepBlocker Tdeep Wdeep)):
    ∃R:SimpleGraph V,∃S:V→U→Prop,
      R≤Q ∧ (∀v z,S v z→H v z) ∧
      HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=m+1)) (ordinaryHostResources R S) ∧
      HasOrdinaryWheelDecomposition R S (m+1) ∧
      (Q\R).support⊆(X:Set V) ∧ (∀v z,H v z∧¬S v z→v∈X∧z∈Z) ∧
      (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤
        limit+((3*(Kcap+Dmax)+Dmax*(m+1):ℕ):ℝ)) ∧
      Disjoint (ordinaryPhysicalGraph R S) (ordinaryDeepBlocker Tdeep Wdeep):=by
  obtain ⟨W,C,hWdis,hCdis,hWdec,hWs,hWinner,hCdec,havoid,hWdeep,hCdeep,houtR,houtS,hrim,hrow,hcol⟩:=
    ordinary_pairing_endpoint_wheel_families_avoiding_deep m hm Q F H X Tdeep Z Wdeep x u hTX hWZ hx hu A B T Y hA hB hY hQr hHr hHc hFroot
      Kcap Dmax hKcap hBsize hYsize hmemA hmemB Lconf limit bcount hLconf hF hcount hbudget selected
  have hcoverR:∀v∉X,∀w,Q.Adj v w→(wheelFamilyRim C).Adj v w:=by
    intro v hv w hvw
    obtain ⟨i,hi⟩:=hxcover v hv
    apply (houtR v hv w).mpr
    exact ⟨i,hi.symm,(hQr i w).mp (by simpa only [hi] using hvw)⟩
  have hcoverS:∀v∉X,∀z,H v z→wheelFamilySpokes C v z:=by
    intro v hv z hvz
    obtain ⟨i,hi⟩:=hxcover v hv
    apply (houtS v hv z).mpr
    exact ⟨i,hi.symm,(hHr i z).mp (by simpa only [hi] using hvz)⟩
  have hcoverHub:∀z∉Z,∀v,H v z→wheelFamilySpokes W v z:=by
    intro z hz v hvz
    obtain ⟨j,hj⟩:=hucover z hz
    apply (hWs v z).mpr
    exact ⟨j,hj,(hHc j v).mp (by simpa only [hj] using hvz)⟩
  have hrimR:∀v,((wheelFamilyRim C).degree v:ℝ)≤((2*(Kcap+Dmax):ℕ):ℝ):=by
    intro v;exact_mod_cast hrim v
  have hrowR:∀v,((Finset.univ.filter (wheelFamilySpokes C v)).card:ℝ)≤((Kcap+Dmax:ℕ):ℝ):=by
    intro v;exact_mod_cast hrow v
  have hcolR:∀z,((Finset.univ.filter (fun v=>wheelFamilySpokes C v z)).card:ℝ)≤((Dmax*(m+1):ℕ):ℝ):=by
    intro z;exact_mod_cast hcol z
  apply ordinary_combine_boundary_wheel_families_avoiding (m+1) Q F H X Z W C
    (ordinaryDeepRimBlocker Tdeep) (ordinaryDeepSpokeBlocker Tdeep Wdeep)
    hWdis hCdis hWdec hCdec havoid hWdeep hCdeep hcoverR hcoverS hcoverHub
    limit ((2*(Kcap+Dmax):ℕ):ℝ) ((Kcap+Dmax:ℕ):ℝ) ((Dmax*(m+1):ℕ):ℝ)
    ((3*(Kcap+Dmax)+Dmax*(m+1):ℕ):ℝ) hWinner hrimR hrowR hcolR
  · exact_mod_cast (show 2*(Kcap+Dmax)+(Kcap+Dmax)≤3*(Kcap+Dmax)+Dmax*(m+1) by omega)
  · exact_mod_cast (show Dmax*(m+1)≤3*(Kcap+Dmax)+Dmax*(m+1) by omega)
end Oberwolfach
