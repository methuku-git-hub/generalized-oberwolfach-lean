module

public import Oberwolfach.OrdinaryTriangleRowBoundary
public import Oberwolfach.SelectedHubFactorWheels
public import Oberwolfach.PhysicalWheelFamilies
public import Oberwolfach.OrdinaryWheelRemainders

@[expose] public section

/-! The deterministic ordinary triangle boundary stage, using the actual
jointly selected hub and endpoint factors. The inner physical graph is
identified exactly, and every exterior incidence is covered. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I J:Type} [Fintype V] [Fintype U] [Fintype I] [Fintype J]
  [DecidableEq V] [DecidableEq U] [DecidableEq I] [DecidableEq J]

theorem ordinary_triangle_boundary_finish (Q F:SimpleGraph V) (H:V→U→Prop)
    (X:Finset V) (Z:Finset U) (x:I↪V) (u:J↪U)
    (hx:∀ i,x i∉X) (hu:∀ j,u j∉Z)
    (hxcover:∀ a∉X,∃ i,x i=a) (hucover:∀ z∉Z,∃ j,u j=z)
    (A:I→Finset V) (B:I→Finset U) (T Y:J→Finset V)
    (hA:∀ i,A i⊆X) (hB:∀ i,B i⊆Z) (hY:∀ j,Y j⊆X)
    (hQr:∀ i a,Q.Adj (x i) a↔a∈A i)
    (hHr:∀ i z,H (x i) z↔z∈B i)
    (hHc:∀ j a,H a (u j)↔a∈Y j)
    (hFroot:∀ i,∀ a∈A i,¬F.Adj (x i) a)
    (D:∀ j,Finset (LocalOrdinaryCycle Q F (T j) 3))
    (hD:∀ j,∀ C∈D j,∀ C'∈D j,C≠C'→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices C'))
    (hDcover:∀ j,(D j).biUnion localOrdinaryVertices=Y j)
    (hDdis:∀ i j,i≠j→Disjoint (localOrdinaryFactorGraph (D i)) (localOrdinaryFactorGraph (D j)))
    (hAB:∀ i,Disjoint ((A i).image Sum.inl) ((B i).image Sum.inr))
    (M:∀ i,Finset (EndpointTriangle (ordinaryPhysicalGraph Q H) (ordinaryPhysicalGraph F (fun _ _=>False))
      ((A i).image Sum.inl) ((B i).image Sum.inr)))
    (hM:∀ i,∀ C∈M i,∀ C'∈M i,C≠C'→Disjoint C.val C'.val)
    (hMcover:∀ i,(M i).biUnion endpointTriangleVertices=(A i).image Sum.inl∪(B i).image Sum.inr)
    (hMdis:∀ i j,i≠j→Disjoint (endpointFactorGraph (hAB i) (M i)) (endpointFactorGraph (hAB j) (M j)))
    (hmixed:∀ j i,Disjoint ((localOrdinaryFactorGraph (D j)).map (Function.Embedding.inl:V↪V⊕U))
      (endpointFactorGraph (hAB i) (M i))):
    ∃ R:SimpleGraph V,∃ S:V→U→Prop,
      R≤Q ∧ (∀ a z,S a z→H a z) ∧ HasOrdinaryWheelDecomposition R S 3 ∧
      (Q\R).support⊆(X:Set V) ∧
      (∀ a z,H a z∧¬S a z→a∈X∧z∈Z) ∧
      spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)=
        (⨆ j,(localOrdinaryFactorGraph (D j)).map (Function.Embedding.inl:V↪V⊕U))⊔
          (⨆ i,endpointFactorGraph (hAB i) (M i)):=by
  obtain ⟨W,_hW,hWr,hWs,_hWdis,hWdec⟩:=selected_hub_factor_wheels Q F H 3 T Y u D hD hDcover
    (fun j a ha=>(hHc j a).mpr ha) hDdis
  obtain ⟨C,_hC,_hCdis,hCdec,hCinner,hCout⟩:=ordinary_triangle_row_boundary Q F H X Z x A B hx hA hB
    (fun i a ha=>(hQr i a).mpr ha) (fun i z hz=>(hHr i z).mpr hz) hFroot hAB M hM hMcover hMdis
  let D₀:=wheelFamilyRim W
  let E₀:=wheelFamilySpokes W
  let D₁:=wheelFamilyRim C
  let E₁:=wheelFamilySpokes C
  let Ω:=ordinaryInnerVertices X Z
  have hDsupport:∀ a b,D₀.Adj a b→a∈X∧b∈X:=by
    intro a b hab
    rw [show D₀=(⨆ j,localOrdinaryFactorGraph (D j)) from hWr] at hab
    obtain ⟨j,hj⟩:=SimpleGraph.iSup_adj.mp hab
    have hh:=(spanningRestriction_adj Q (Y j) a b).mp
      (localOrdinaryFactorGraph_restriction (D j) (Y j) (hDcover j) hj)
    exact ⟨hY j hh.2.1,hY j hh.2.2⟩
  have hEout (a:V) (z:U) (he:E₀ a z):z∉Z:=by
    obtain ⟨j,hj,_⟩:=(hWs a z).mp he
    exact hj ▸ hu j
  have hE₁in (a:V) (z:U) (he:E₁ a z):z∈Z:=by
    by_contra hz
    have ha:(⨆ i,ordinaryWheelPhysicalGraph (C i)).Adj (Sum.inr z) (Sum.inl a):=by
      rw [←wheelFamily_physical_graph];exact he
    have hn:Sum.inr z∉X.image Sum.inl∪Z.image Sum.inr:=by simpa using hz
    obtain ⟨i,hi,_⟩:=(hCout (Sum.inr z) hn (Sum.inl a)).mp ha
    exact Sum.inl_ne_inr hi
  have hinner₁:spanningRestriction (ordinaryPhysicalGraph D₁ E₁) Ω=
      ⨆ i,endpointFactorGraph (hAB i) (M i):=by
    rw [wheelFamily_physical_graph];exact hCinner
  have hdisR:Disjoint D₀ D₁:=by
    apply disjoint_iff_inf_le.mpr
    intro a b hab
    have hm:((⨆ i,endpointFactorGraph (hAB i) (M i))).Adj (Sum.inl a) (Sum.inl b):=by
      rw [←hinner₁]
      exact (spanningRestriction_adj _ _ _ _).mpr ⟨hab.2,
        (ordinaryInnerVertices_left X Z a).mpr (hDsupport a b hab.1).1,
        (ordinaryInnerVertices_left X Z b).mpr (hDsupport a b hab.1).2⟩
    obtain ⟨i,hi⟩:=SimpleGraph.iSup_adj.mp hm
    have hd:=hab.1
    rw [show D₀=(⨆ j,localOrdinaryFactorGraph (D j)) from hWr] at hd
    obtain ⟨j,hj⟩:=SimpleGraph.iSup_adj.mp hd
    have hmix:=hmixed j i
    rw [graph_map_inl_physical] at hmix
    exact (disjoint_iff_inf_le.mp hmix) (v:=Sum.inl a) (w:=Sum.inl b) ⟨hj,hi⟩
  have hdisS:∀ a z,¬(E₀ a z∧E₁ a z):=by
    rintro a z ⟨h0,h1⟩;exact hEout a z h0 (hE₁in a z h1)
  let R:=D₀⊔D₁
  let S:V→U→Prop:=fun a z=>E₀ a z∨E₁ a z
  have hdec:HasOrdinaryWheelDecomposition R S 3:=
    ordinary_wheel_decomposition_union D₀ D₁ E₀ E₁ 3 hWdec hCdec hdisR hdisS
  have hrow (a:V) (ha:a∉X) (v:V⊕U)
      (hav:(ordinaryPhysicalGraph Q H).Adj (Sum.inl a) v):
      (ordinaryPhysicalGraph D₁ E₁).Adj (Sum.inl a) v:=by
    rw [wheelFamily_physical_graph]
    apply (hCout (Sum.inl a) (by simpa using ha) v).mpr
    obtain ⟨i,hi⟩:=hxcover a ha
    refine ⟨i,congrArg Sum.inl hi,?_⟩
    cases v with
    | inl b=>
      have hb:b∈A i:=(hQr i b).mp (hi.symm ▸ hav)
      simp [hb]
    | inr z=>
      have hz:z∈B i:=(hHr i z).mp (hi.symm ▸ hav)
      simp [hz]
  refine ⟨R,S,(sup_le (wheelFamily_subhost W).1 (wheelFamily_subhost C).1),
    (fun a z h=>h.elim ((wheelFamily_subhost W).2 a z) ((wheelFamily_subhost C).2 a z)),hdec,?_,?_,?_⟩
  · intro a ha
    by_contra hn
    obtain ⟨b,hb⟩:=ha
    exact hb.2 (Or.inr (hrow a hn (Sum.inl b) hb.1))
  · intro a z haz
    constructor
    · by_contra hn;exact haz.2 (Or.inr (hrow a hn (Sum.inr z) haz.1))
    · by_contra hn
      obtain ⟨j,hj⟩:=hucover z hn
      exact haz.2 (Or.inl ((hWs a z).mpr ⟨j,hj,(hHc j a).mp (hj.symm ▸ haz.1)⟩))
  · have hinner₀:spanningRestriction (ordinaryPhysicalGraph D₀ E₀) Ω=
        ⨆ j,(localOrdinaryFactorGraph (D j)).map (Function.Embedding.inl:V↪V⊕U):=by
      ext a b
      rw [spanningRestriction_adj,SimpleGraph.iSup_adj]
      cases a with
      | inl a=>
        cases b with
        | inl b=>
          simp only [graph_map_inl_physical,ordinaryPhysicalGraph]
          constructor
          · intro h
            rw [show D₀=(⨆ j,localOrdinaryFactorGraph (D j)) from hWr] at h
            exact SimpleGraph.iSup_adj.mp h.1
          · intro h
            have hd:D₀.Adj a b:=by rw [show D₀=(⨆ j,localOrdinaryFactorGraph (D j)) from hWr];exact SimpleGraph.iSup_adj.mpr h
            exact ⟨hd,(ordinaryInnerVertices_left X Z a).mpr (hDsupport a b hd).1,
              (ordinaryInnerVertices_left X Z b).mpr (hDsupport a b hd).2⟩
        | inr b=>
          simp only [graph_map_inl_physical,ordinaryPhysicalGraph,exists_false,iff_false]
          rintro ⟨hab,_,hb⟩;exact hEout a b hab ((ordinaryInnerVertices_right X Z b).mp hb)
      | inr a=>
        cases b with
        | inl b=>
          simp only [graph_map_inl_physical,ordinaryPhysicalGraph,exists_false,iff_false]
          rintro ⟨hab,ha,_⟩;exact hEout b a hab ((ordinaryInnerVertices_right X Z a).mp ha)
        | inr b=>simp [graph_map_inl_physical,ordinaryPhysicalGraph]
    change spanningRestriction (ordinaryPhysicalGraph (D₀⊔D₁) (fun a z=>E₀ a z∨E₁ a z)) Ω=_
    rw [ordinaryPhysicalGraph_sup,←hinner₀,←hinner₁]
    ext a b
    simp only [spanningRestriction_adj,SimpleGraph.sup_adj]
    tauto

end Oberwolfach
