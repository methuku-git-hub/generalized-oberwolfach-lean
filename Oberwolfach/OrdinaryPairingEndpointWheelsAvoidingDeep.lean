module

public import Oberwolfach.OrdinaryPairingHubWheelsAvoidingDeep
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

theorem ordinary_pairing_endpoint_wheel_families_avoiding_deep
    (m:ℕ) (hm:3≤m) (Q F:SimpleGraph V) (H:V→U→Prop)
    (X Tdeep:Finset V) (Z Wdeep:Finset U) (x:I↪V) (u:J↪U)
    (hTX:Tdeep⊆X) (hWZ:Wdeep⊆Z)
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
      2*(limit+Tdeep.card+2*((Kcap+Dmax:ℕ):ℝ))+((Dmax:ℝ)+Tdeep.card)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax<bcount)
    (selected:OrdinaryPairingSelectedFactorsAvoiding m Q F H A B T Y limit (ordinaryDeepBlocker Tdeep Wdeep)):
    ∃(W:(Σj,selected.selected.hub j)→OrdinaryWheel Q F H (m+1))
      (C:(Σi,B i)→OrdinaryWheel Q F H (m+1)),
      (∀a b,a≠b→Disjoint (ordinaryWheelResources (W a)) (ordinaryWheelResources (W b))) ∧
      (∀a b,a≠b→Disjoint (ordinaryWheelResources (C a)) (ordinaryWheelResources (C b))) ∧
      HasOrdinaryWheelDecomposition (wheelFamilyRim W) (wheelFamilySpokes W) (m+1) ∧
      (∀v z,wheelFamilySpokes W v z↔∃j,u j=z∧v∈Y j) ∧
      (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph (wheelFamilyRim W) (wheelFamilySpokes W))
        (ordinaryInnerVertices X Z)).degree w:ℝ)≤limit) ∧
      HasOrdinaryWheelDecomposition (wheelFamilyRim C) (wheelFamilySpokes C) (m+1) ∧
      (∀i,Disjoint (ordinaryWheelResources (C i)) (ordinaryHostResources (wheelFamilyRim W) (wheelFamilySpokes W))) ∧
      Disjoint (ordinaryPhysicalGraph (wheelFamilyRim W) (wheelFamilySpokes W)) (ordinaryDeepBlocker Tdeep Wdeep) ∧
      (∀i,Disjoint (ordinaryWheelResources (C i)) (ordinaryHostResources (ordinaryDeepRimBlocker Tdeep) (ordinaryDeepSpokeBlocker Tdeep Wdeep))) ∧
      (∀v∉X,∀w,(wheelFamilyRim C).Adj v w↔∃i,v=x i∧w∈A i) ∧
      (∀v∉X,∀z,wheelFamilySpokes C v z↔∃i,v=x i∧z∈B i) ∧
      (∀v,(wheelFamilyRim C).degree v≤2*(Kcap+Dmax)) ∧
      (∀v,(Finset.univ.filter (wheelFamilySpokes C v)).card≤Kcap+Dmax) ∧
      (∀z,(Finset.univ.filter (fun v=>wheelFamilySpokes C v z)).card≤Dmax*(m+1)):=by
  obtain ⟨W,hWdis,hWdec,hWs,hDsupport,hEspoke,hDdeg,hEdeg,hWinner,hhold,hWdeep⟩:=
    ordinary_pairing_hub_wheel_preparation_avoiding_deep m Q F H X Tdeep Z Wdeep u hWZ hu A B T Y hA hB hY
      (fun j v hv=>(hHc j v).mpr hv) Dmax hYsize limit selected
  have hrowcross:∀i j,i≠j→Disjoint (selected.selected.row i).graph (selected.selected.row j).graph:=by
    intro i j hij
    have hh:=selected.selected.cross (Sum.inr i) (Sum.inr j) (by simpa using hij)
    simpa only [Sum.elim_inr] using hh
  let D₀:=wheelFamilyRim W⊔ordinaryDeepRimBlocker Tdeep
  let E₀:=fun v z=>wheelFamilySpokes W v z∨ordinaryDeepSpokeBlocker Tdeep Wdeep v z
  have hedge:∀i,∀v∈A i,Q.Adj (x i) v ∧ ¬D₀.Adj (x i) v ∧ ¬F.Adj (x i) v:=by
    intro i v hv
    refine ⟨(hQr i v).mpr hv,?_,hFroot i v hv⟩
    intro hh
    rcases hh with hh|hh
    · exact hx i (hDsupport (x i) v hh).1
    · exact hx i (hTX ((ordinary_deep_rim_blocker_adj Tdeep (x i) v).mp hh).2.1)
  have hroot:∀i,∀z∈B i,H (x i) z ∧ ¬E₀ (x i) z:=by
    intro i z hz
    refine ⟨(hHr i z).mpr hz,?_⟩
    intro hh
    rcases hh with hh|hh
    · exact hx i (hEspoke (x i) z hh).1
    · exact hx i (hTX hh.1)
  have hD₀:∀v∈X,(D₀.degree v:ℝ)≤limit+Tdeep.card:=by
    intro v hv
    have hdeg:=graph_degree_sup_le (wheelFamilyRim W) (ordinaryDeepRimBlocker Tdeep) v
    have hdeep:=ordinary_deep_rim_blocker_degree Tdeep v
    have hdeepR:((ordinaryDeepRimBlocker Tdeep).degree v:ℝ)≤Tdeep.card:=by exact_mod_cast hdeep
    have hdegR:(D₀.degree v:ℝ)≤((wheelFamilyRim W).degree v:ℝ)+((ordinaryDeepRimBlocker Tdeep).degree v:ℝ):=by
      exact_mod_cast hdeg
    linarith only [hdegR,hDdeg v,hdeepR]
  have hE₀:∀z,((Finset.univ.filter (fun v=>E₀ v z)).card:ℝ)≤(Dmax:ℝ)+Tdeep.card:=by
    intro z
    have he:Finset.univ.filter (fun v=>E₀ v z)=
        (Finset.univ.filter (fun v=>wheelFamilySpokes W v z))∪
        (Finset.univ.filter (fun v=>ordinaryDeepSpokeBlocker Tdeep Wdeep v z)):=by
      ext v;simp [E₀]
    have hsub:(Finset.univ.filter (fun v=>ordinaryDeepSpokeBlocker Tdeep Wdeep v z))⊆Tdeep:=by
      intro v hv
      exact (Finset.mem_filter.mp hv).2.1
    have hc:=Finset.card_union_le (Finset.univ.filter (fun v=>wheelFamilySpokes W v z))
      (Finset.univ.filter (fun v=>ordinaryDeepSpokeBlocker Tdeep Wdeep v z))
    have ht:=Finset.card_le_card hsub
    have hcR:((Finset.univ.filter (fun v=>E₀ v z)).card:ℝ)≤
        ((Finset.univ.filter (fun v=>wheelFamilySpokes W v z)).card:ℝ)+
        ((Finset.univ.filter (fun v=>ordinaryDeepSpokeBlocker Tdeep Wdeep v z)).card:ℝ):=by
      rw [he];exact_mod_cast hc
    have htR:((Finset.univ.filter (fun v=>ordinaryDeepSpokeBlocker Tdeep Wdeep v z)).card:ℝ)≤Tdeep.card:=by exact_mod_cast ht
    linarith only [hcR,hEdeg z,htR]
  have hhold₀:∀i,Disjoint (selected.selected.row i).graph (ordinaryPhysicalGraph D₀ E₀):=by
    intro i
    rw [show ordinaryPhysicalGraph D₀ E₀=ordinaryPhysicalGraph (wheelFamilyRim W) (wheelFamilySpokes W)⊔
      ordinaryDeepBlocker Tdeep Wdeep from ordinaryPhysicalGraph_sup _ _ _ _]
    apply disjoint_sup_right.mpr
    refine ⟨hhold i,?_⟩
    have hh:=selected.avoids (Sum.inr i)
    simpa only [Sum.elim_inr] using hh
  obtain ⟨C,hC,hCdis,hCdec,houtR,houtS,hrim,hrow,hcol⟩:=endpoint_boundary_completion Q D₀ F H
    E₀ X x A B hx hA hedge hroot selected.selected.row hrowcross hhold₀ (m+1) Kcap Dmax
    (by omega) hKcap hBsize hmemA hmemB Lconf (limit+Tdeep.card) (Dmax+Tdeep.card) bcount hLconf hF
    (by intro v hv;convert hD₀ v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro z;convert hE₀ z using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hcount hbudget
  have hCold:∀i,Disjoint (ordinaryWheelResources (C i)) (ordinaryHostResources (wheelFamilyRim W) (wheelFamilySpokes W)):=by
    intro i
    have h:Disjoint (ordinaryWheelResources (C i)) (ordinaryHostResources D₀ E₀):=(hC i).2.2
    rw [show ordinaryHostResources D₀ E₀=ordinaryHostResources (wheelFamilyRim W) (wheelFamilySpokes W) ∪
      ordinaryHostResources (ordinaryDeepRimBlocker Tdeep) (ordinaryDeepSpokeBlocker Tdeep Wdeep) from ordinaryHostResources_union _ _ _ _] at h
    exact (Finset.disjoint_union_right.mp h).1
  have hCdeep:∀i,Disjoint (ordinaryWheelResources (C i)) (ordinaryHostResources (ordinaryDeepRimBlocker Tdeep) (ordinaryDeepSpokeBlocker Tdeep Wdeep)):=by
    intro i
    have h:Disjoint (ordinaryWheelResources (C i)) (ordinaryHostResources D₀ E₀):=(hC i).2.2
    rw [show ordinaryHostResources D₀ E₀=ordinaryHostResources (wheelFamilyRim W) (wheelFamilySpokes W) ∪
      ordinaryHostResources (ordinaryDeepRimBlocker Tdeep) (ordinaryDeepSpokeBlocker Tdeep Wdeep) from ordinaryHostResources_union _ _ _ _] at h
    exact (Finset.disjoint_union_right.mp h).2
  exact ⟨W,C,hWdis,hCdis,hWdec,hWs,hWinner,hCdec,hCold,hWdeep,hCdeep,houtR,houtS,hrim,hrow,hcol⟩
end Oberwolfach
