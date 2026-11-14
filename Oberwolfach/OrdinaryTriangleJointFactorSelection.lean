module

public import Oberwolfach.OrdinaryTriangleSelectedFactors
public import Oberwolfach.BoundaryMixedWitnessSelection

@[expose] public section
/-! Select the actual hub cycle factors and triangle endpoint factors
jointly, retaining the mixed physical-edge disjointness and inner-degree
budget needed by the boundary finish. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_joint_factor_selection (p:ℝ) (hp:0<p):
    ∃n₀:ℕ,2≤n₀ ∧ ∀(V U I J:Type) [Fintype V] [Fintype U] [Fintype I] [Fintype J]
      [DecidableEq V] [DecidableEq U] [DecidableEq I] [DecidableEq J],n₀≤Fintype.card (V⊕U)→
    ∀(Q F:SimpleGraph V) (H:V→U→Prop) (A:I→Finset V) (B:I→Finset U) (T Y:J→Finset V)
      (hAB:∀i,Disjoint ((A i).image Sum.inl) ((B i).image Sum.inr))
      (N D:ℕ) (G:SimpleGraph (V⊕U)) (S:Fin N→Finset (V⊕U))
      (Choice:Fin N→Type) (Valid:∀i,Choice i→Prop) (graph:∀i,Choice i→SimpleGraph (V⊕U))
      (x:I↪Fin N) (u:J↪Fin N) (hsep:∀i j,x i≠u j)
      (rowOf:∀i,Choice (x i)→Finset (EndpointTriangle (ordinaryPhysicalGraph Q H)
        (ordinaryPhysicalGraph F (fun _ _=>False)) ((A i).image Sum.inl) ((B i).image Sum.inr)))
      (hubOf:∀j,Choice (u j)→Finset (LocalOrdinaryCycle Q F (T j) 3)),
    (∀i c,Valid (x i) c→
      (∀C∈rowOf i c,∀C'∈rowOf i c,C≠C'→Disjoint C.val C'.val) ∧
      (rowOf i c).biUnion endpointTriangleVertices=(A i).image Sum.inl∪(B i).image Sum.inr ∧
      graph (x i) c=endpointFactorGraph (hAB i) (rowOf i c)) →
    (∀j c,Valid (u j) c→
      (∀C∈hubOf j c,∀C'∈hubOf j c,C≠C'→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices C')) ∧
      (hubOf j c).biUnion localOrdinaryVertices=Y j ∧
      graph (u j) c=(localOrdinaryFactorGraph (hubOf j c)).map (Function.Embedding.inl:V↪V⊕U)) →
    (∀i j,i≠j→((S i∩S j).card:ℝ)≤p^2*Fintype.card (V⊕U)) →
    (∀v,((Finset.univ.filter (fun i=>v∈S i)).card:ℝ)≤p*Fintype.card (V⊕U)) →
    (∀i,∀K:SimpleGraph (V⊕U),K≤spanningRestriction G (S i)→
      (∀v,(K.degree v:ℝ)≤D*(p*Real.sqrt p*Fintype.card (V⊕U))+
        D*(Nat.ceil (4*(p*Real.sqrt p*Fintype.card (V⊕U))):ℝ))→
      ∃C:Choice i,Valid i C ∧ graph i C≤spanningRestriction G (S i) ∧
        (∀v,(graph i C).degree v≤D) ∧ Disjoint (graph i C) K) →
    Nonempty (OrdinaryTriangleSelectedFactors Q F H A B T Y hAB (D*(p*Fintype.card (V⊕U)))):=by
  obtain ⟨n₀,hn₀,hselect⟩:=mixed_boundary_factor_selection p hp
  refine ⟨n₀,hn₀,?_⟩
  intro V U I J _ _ _ _ _ _ _ _ hn Q F H A B T Y hAB N D G S Choice Valid graph x u hsep rowOf hubOf
    hrow hhub hinter hmem hsingle
  let Row:=fun i:I=>Finset (EndpointTriangle (ordinaryPhysicalGraph Q H)
    (ordinaryPhysicalGraph F (fun _ _=>False)) ((A i).image Sum.inl) ((B i).image Sum.inr))
  let Hub:=fun j:J=>Finset (LocalOrdinaryCycle Q F (T j) 3)
  let rowValid:=fun (i:I) (M:Row i)=>
    (∀C∈M,∀C'∈M,C≠C'→Disjoint C.val C'.val) ∧ M.biUnion endpointTriangleVertices=(A i).image Sum.inl∪(B i).image Sum.inr
  let hubValid:=fun (j:J) (M:Hub j)=>
    (∀C∈M,∀C'∈M,C≠C'→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices C')) ∧ M.biUnion localOrdinaryVertices=Y j
  let rowGraph:=fun (i:I) (M:Row i)=>endpointFactorGraph (hAB i) M
  let hubGraph:=fun (j:J) (M:Hub j)=>(localOrdinaryFactorGraph M).map (Function.Embedding.inl:V↪V⊕U)
  have hr:∀i c,Valid (x i) c→ rowValid i (rowOf i c) ∧ graph (x i) c=rowGraph i (rowOf i c):=by
    intro i c hc
    obtain ⟨h1,h2,h3⟩:=hrow i c hc
    exact ⟨⟨h1,h2⟩,h3⟩
  have hh:∀j c,Valid (u j) c→hubValid j (hubOf j c) ∧ graph (u j) c=hubGraph j (hubOf j c):=by
    intro j c hc
    obtain ⟨h1,h2,h3⟩:=hhub j c hc
    exact ⟨⟨h1,h2⟩,h3⟩
  obtain ⟨R,M,hRv,hMv,hRdis,hMdis,hmix,hdeg⟩:=hselect (V⊕U) I J hn N D G S Choice Valid graph x u hsep
    Row Hub rowValid hubValid rowGraph hubGraph rowOf hubOf hr hh hinter hmem hsingle
  refine ⟨⟨M,fun j=>(hMv j).1,fun j=>(hMv j).2,?_,R,fun i=>(hRv i).1,fun i=>(hRv i).2,hRdis,?_,?_⟩⟩
  · intro i j hij
    have hd:=hMdis i j hij
    dsimp only [hubGraph] at hd
    rw [graph_map_inl_physical,graph_map_inl_physical] at hd
    apply disjoint_iff_inf_le.mpr
    intro a b hab
    exact (disjoint_iff_inf_le.mp hd) (v:=Sum.inl a) (w:=Sum.inl b) ⟨hab.1,hab.2⟩
  · intro j i
    exact (hmix i j).symm
  · intro w
    have hsub:((⨆j,(localOrdinaryFactorGraph (M j)).map (Function.Embedding.inl:V↪V⊕U))⊔
        (⨆i,endpointFactorGraph (hAB i) (R i)))≤(⨆i,rowGraph i (R i))⊔(⨆j,hubGraph j (M j)):=by
      dsimp [rowGraph,hubGraph]
      exact le_of_eq (sup_comm _ _)
    have hdegree:(((⨆j,(localOrdinaryFactorGraph (M j)).map (Function.Embedding.inl:V↪V⊕U))⊔
        (⨆i,endpointFactorGraph (hAB i) (R i))).degree w:ℝ)≤
        (((⨆i,rowGraph i (R i))⊔(⨆j,hubGraph j (M j))).degree w:ℝ):=by
      exact_mod_cast (SimpleGraph.degree_le_of_le hsub (v:=w))
    exact hdegree.trans (hdeg w)
end Oberwolfach
