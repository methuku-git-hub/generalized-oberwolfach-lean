module

public import Oberwolfach.OrdinaryPairingSelectedFactorsAvoiding
public import Oberwolfach.OrdinaryDeepBlocker
public import Oberwolfach.SelectedHubFactorWheels
public import Oberwolfach.PhysicalWheelFamilies

@[expose] public section
/-! Convert the selected hub factors to actual wheels, retain their degree
    bounds, and keep every selected endpoint pairing physically disjoint. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I J:Type} [Fintype V] [Fintype U] [Fintype I] [Fintype J]
  [DecidableEq V] [DecidableEq U] [DecidableEq I] [DecidableEq J]

theorem ordinary_pairing_hub_wheel_preparation_avoiding_deep
    (m:ℕ) (Q F:SimpleGraph V) (H:V→U→Prop) (X Tdeep:Finset V) (Z Wdeep:Finset U) (u:J↪U)
    (hWZ:Wdeep⊆Z)
    (hu:∀j,u j∉Z) (A:I→Finset V) (B:I→Finset U) (T Y:J→Finset V)
    (hA:∀i,A i⊆X) (hB:∀i,B i⊆Z) (hY:∀j,Y j⊆X)
    (hH:∀j,∀v∈Y j,H v (u j)) (Dmax:ℕ) (hYsize:∀j,(Y j).card≤Dmax)
    (limit:ℝ) (selected:OrdinaryPairingSelectedFactorsAvoiding m Q F H A B T Y limit (ordinaryDeepBlocker Tdeep Wdeep)):
    ∃W:(Σj,selected.selected.hub j)→OrdinaryWheel Q F H (m+1),
      (∀i j,i≠j→Disjoint (ordinaryWheelResources (W i)) (ordinaryWheelResources (W j))) ∧
      HasOrdinaryWheelDecomposition (wheelFamilyRim W) (wheelFamilySpokes W) (m+1) ∧
      (∀v z,wheelFamilySpokes W v z↔∃j,u j=z ∧ v∈Y j) ∧
      (∀v w,(wheelFamilyRim W).Adj v w→v∈X∧w∈X) ∧
      (∀v z,wheelFamilySpokes W v z→v∈X∧z∉Z) ∧
      (∀v,((wheelFamilyRim W).degree v:ℝ)≤limit) ∧
      (∀z,((Finset.univ.filter (fun v=>wheelFamilySpokes W v z)).card:ℝ)≤Dmax) ∧
      (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph (wheelFamilyRim W) (wheelFamilySpokes W))
        (ordinaryInnerVertices X Z)).degree w:ℝ)≤limit) ∧
      (∀i,Disjoint (selected.selected.row i).graph (ordinaryPhysicalGraph (wheelFamilyRim W) (wheelFamilySpokes W))) ∧
      Disjoint (ordinaryPhysicalGraph (wheelFamilyRim W) (wheelFamilySpokes W)) (ordinaryDeepBlocker Tdeep Wdeep):=by
  have hcross:∀i j,i≠j→Disjoint (localOrdinaryFactorGraph (selected.selected.hub i)) (localOrdinaryFactorGraph (selected.selected.hub j)):=by
    intro i j hij
    have hh:=selected.selected.cross (Sum.inl i) (Sum.inl j) (by simpa using hij)
    dsimp only [Sum.elim_inl] at hh
    rw [graph_map_inl_physical,graph_map_inl_physical] at hh
    apply disjoint_iff_inf_le.mpr
    intro a b hab
    exact (disjoint_iff_inf_le.mp hh) (v:=Sum.inl a) (w:=Sum.inl b) ⟨hab.1,hab.2⟩
  obtain ⟨W,_hW,hWr,hWs,hdis,hdec⟩:=selected_hub_factor_wheels Q F H (m+1) T Y u selected.selected.hub
    selected.selected.hub_disjoint selected.selected.hub_cover hH hcross
  let D₀:=wheelFamilyRim W
  let E₀:=wheelFamilySpokes W
  let Ω:=ordinaryInnerVertices X Z
  let G:=fun k:J⊕I=>Sum.elim
    (fun j=>(localOrdinaryFactorGraph (selected.selected.hub j)).map (Function.Embedding.inl:V↪V⊕U))
    (fun i=>(selected.selected.row i).graph) k
  have hDsupport:∀v w,D₀.Adj v w→v∈X∧w∈X:=by
    intro v w hvw
    rw [show D₀=⨆j,localOrdinaryFactorGraph (selected.selected.hub j) from hWr] at hvw
    obtain ⟨j,hj⟩:=SimpleGraph.iSup_adj.mp hvw
    have hh:=(spanningRestriction_adj Q (Y j) v w).mp
      (localOrdinaryFactorGraph_restriction (selected.selected.hub j) (Y j) (selected.selected.hub_cover j) hj)
    exact ⟨hY j hh.2.1,hY j hh.2.2⟩
  have hEspoke:∀v z,E₀ v z→v∈X∧z∉Z:=by
    intro v z hvz
    obtain ⟨j,hj,hv⟩:=(hWs v z).mp hvz
    exact ⟨hY j hv,hj ▸ hu j⟩
  have hsub:(D₀.map (Function.Embedding.inl:V↪V⊕U))≤⨆k,G k:=by
    intro x y hxy
    rw [graph_map_inl_physical] at hxy
    cases x with
    | inl v=>
      cases y with
      | inl w=>
        change D₀.Adj v w at hxy
        rw [show D₀=⨆j,localOrdinaryFactorGraph (selected.selected.hub j) from hWr] at hxy
        obtain ⟨j,hj⟩:=SimpleGraph.iSup_adj.mp hxy
        apply SimpleGraph.iSup_adj.mpr
        refine ⟨Sum.inl j,?_⟩
        change ((localOrdinaryFactorGraph (selected.selected.hub j)).map (Function.Embedding.inl:V↪V⊕U)).Adj _ _
        rw [graph_map_inl_physical]
        exact hj
      | inr z=>cases hxy
    | inr z=>cases y <;> cases hxy
  have hdegree (v:V):((D₀.degree v):ℝ)≤limit:=by
    have he:=SimpleGraph.degree_map_apply D₀ (Function.Embedding.inl:V↪V⊕U) v
    have hh:(D₀.map (Function.Embedding.inl:V↪V⊕U)).degree (Sum.inl v)≤(⨆k,G k).degree (Sum.inl v):=
      SimpleGraph.degree_le_of_le hsub
    change (D₀.map (Function.Embedding.inl:V↪V⊕U)).degree (Sum.inl v)=D₀.degree v at he
    rw [he] at hh
    exact (Nat.cast_le.mpr hh).trans (selected.selected.inner_degree (Sum.inl v))
  have hcol (z:U):((Finset.univ.filter (fun v=>E₀ v z)).card:ℝ)≤Dmax:=by
    by_cases hz:∃j,u j=z
    · obtain ⟨j,rfl⟩:=hz
      have he:Finset.univ.filter (fun v=>E₀ v (u j))=Y j:=by
        ext v
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]
        change wheelFamilySpokes W v (u j) ↔ v∈Y j
        rw [hWs]
        constructor
        · rintro ⟨k,hk,hv⟩
          have heq:k=j:=u.injective hk
          simpa only [heq] using hv
        · intro hv
          exact ⟨j,rfl,hv⟩
      rw [he]
      exact_mod_cast hYsize j
    · have he:Finset.univ.filter (fun v=>E₀ v z)=∅:=by
        ext v
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]
        constructor
        · intro hv
          obtain ⟨j,hj,_⟩:=(hWs v z).mp hv
          exact False.elim (hz ⟨j,hj⟩)
        · intro hv
          simp at hv
      rw [he,Finset.card_empty,Nat.cast_zero]
      positivity
  have hinner:spanningRestriction (ordinaryPhysicalGraph D₀ E₀) Ω=
      D₀.map (Function.Embedding.inl:V↪V⊕U):=by
    ext a b
    rw [spanningRestriction_adj,graph_map_inl_physical]
    cases a with
    | inl a=>
      cases b with
      | inl b=>
        simp only [ordinaryPhysicalGraph]
        constructor
        · exact fun h=>h.1
        · intro h
          exact ⟨h,(ordinaryInnerVertices_left X Z a).mpr (hDsupport a b h).1,
            (ordinaryInnerVertices_left X Z b).mpr (hDsupport a b h).2⟩
      | inr z=>
        simp only [ordinaryPhysicalGraph,iff_false]
        rintro ⟨h,_,hz⟩
        exact (hEspoke a z h).2 ((ordinaryInnerVertices_right X Z z).mp hz)
    | inr z=>
      cases b with
      | inl a=>
        simp only [ordinaryPhysicalGraph,iff_false]
        rintro ⟨h,hz,_⟩
        exact (hEspoke a z h).2 ((ordinaryInnerVertices_right X Z z).mp hz)
      | inr w=>simp [ordinaryPhysicalGraph]
  have hinnerDegree (w:V⊕U):((spanningRestriction (ordinaryPhysicalGraph D₀ E₀) Ω).degree w:ℝ)≤limit:=by
    rw [hinner]
    have hh:((D₀.map (Function.Embedding.inl:V↪V⊕U)).degree w:ℝ)≤((⨆k,G k).degree w:ℝ):=by
      exact_mod_cast SimpleGraph.degree_le_of_le hsub
    convert hh.trans (selected.selected.inner_degree w) using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hhold (i:I):Disjoint (selected.selected.row i).graph (ordinaryPhysicalGraph D₀ E₀):=by
    apply disjoint_iff_inf_le.mpr
    intro a b hab
    have hrow:=(spanningRestriction_adj _ _ _ _).mp ((selected.selected.row i).graph_le hab.1)
    have hin (z:V⊕U) (hz:z∈(A i).image Sum.inl∪(B i).image Sum.inr):z∈Ω:=by
      rcases Finset.mem_union.mp hz with hz|hz
      · obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hz
        exact (ordinaryInnerVertices_left X Z v).mpr (hA i hv)
      · obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hz
        exact (ordinaryInnerVertices_right X Z v).mpr (hB i hv)
    have hW:(spanningRestriction (ordinaryPhysicalGraph D₀ E₀) Ω).Adj a b:=
      (spanningRestriction_adj _ _ _ _).mpr ⟨hab.2,hin a hrow.2.1,hin b hrow.2.2⟩
    rw [hinner,graph_map_inl_physical] at hW
    cases a with
    | inl a=>
      cases b with
      | inl b=>
        change D₀.Adj a b at hW
        rw [show D₀=⨆j,localOrdinaryFactorGraph (selected.selected.hub j) from hWr] at hW
        obtain ⟨j,hj⟩:=SimpleGraph.iSup_adj.mp hW
        have hd:=selected.selected.cross (Sum.inl j) (Sum.inr i) (by simp)
        dsimp only [Sum.elim_inl,Sum.elim_inr] at hd
        rw [graph_map_inl_physical] at hd
        exact (disjoint_iff_inf_le.mp hd) (v:=Sum.inl a) (w:=Sum.inl b) ⟨hj,hab.1⟩
      | inr z=>cases hW
    | inr z=>cases b <;> cases hW
  have hDdeep:Disjoint D₀ (ordinaryDeepRimBlocker Tdeep):=by
    apply disjoint_iff_inf_le.mpr
    intro a b hab
    have hD:=(show D₀=⨆j,localOrdinaryFactorGraph (selected.selected.hub j) from hWr) ▸ hab.1
    obtain ⟨j,hj⟩:=SimpleGraph.iSup_adj.mp hD
    have hav:=selected.avoids (Sum.inl j)
    dsimp only [Sum.elim_inl] at hav
    apply (disjoint_iff_inf_le.mp hav) (v:=Sum.inl a) (w:=Sum.inl b)
    constructor
    · rw [graph_map_inl_physical];exact hj
    · exact hab.2
  have hEdeep:∀v z,¬(E₀ v z∧ordinaryDeepSpokeBlocker Tdeep Wdeep v z):=by
    intro v z hh
    exact (hEspoke v z hh.1).2 (hWZ hh.2.2)
  have hdeep:Disjoint (ordinaryPhysicalGraph D₀ E₀) (ordinaryDeepBlocker Tdeep Wdeep):=by
    exact (ordinaryPhysicalGraph_disjoint D₀ (ordinaryDeepRimBlocker Tdeep) E₀
      (ordinaryDeepSpokeBlocker Tdeep Wdeep)).mpr ⟨hDdeep,hEdeep⟩
  exact ⟨W,hdis,hdec,hWs,hDsupport,hEspoke,hdegree,hcol,hinnerDegree,hhold,hdeep⟩
end Oberwolfach
