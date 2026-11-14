module

public import Oberwolfach.OrdinaryTriangleFactorsFromMixedWithAvoid
public import Oberwolfach.OrdinaryLocalFactorAvoidedHost
public import Oberwolfach.EndpointFactorAvoidedHost

@[expose] public section
/-! Transfer the jointly selected fresh factors through earlier physical-edge
deletions and restrict them to the actual surviving boundary classes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I J:Type} [Fintype V] [Fintype U] [Fintype I] [Fintype J]
  [DecidableEq V] [DecidableEq U] [DecidableEq I] [DecidableEq J]

theorem ordinary_triangle_fresh_factors_actual_host_with_avoid
    (Q Q' F:SimpleGraph V) (H H':V→U→Prop) (K:SimpleGraph (V⊕U))
    (A:I→Finset V) (B:I→Finset U) (S₀ T₀:I→Finset (V⊕U)) (T Y:J→Finset V)
    (hST:∀i,Disjoint (S₀ i) (T₀ i))
    (hAB:∀i,Disjoint ((A i).image Sum.inl) ((B i).image Sum.inr))
    (hA:∀i,(A i).image Sum.inl⊆S₀ i) (hB:∀i,(B i).image Sum.inr⊆T₀ i)
    (D:∀j,Finset (LocalOrdinaryCycle Q F (T j) 3))
    (M:∀i,Finset (EndpointTriangle (ordinaryPhysicalGraph Q H) (ordinaryPhysicalGraph F (fun _ _=>False)) (S₀ i) (T₀ i)))
    (hD:∀j,(∀C∈D j,∀C'∈D j,C≠C'→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices C')) ∧
      (D j).biUnion localOrdinaryVertices=Y j)
    (hM:∀i,(∀C∈M i,∀C'∈M i,C≠C'→Disjoint (endpointTriangleVertices C) (endpointTriangleVertices C')) ∧
      (M i).biUnion endpointTriangleVertices=(A i).image Sum.inl∪(B i).image Sum.inr)
    (hDavoid:∀j,Disjoint ((localOrdinaryFactorGraph (D j)).map (Function.Embedding.inl:V↪V⊕U)) K)
    (hMavoid:∀i,Disjoint (endpointFactorGraph (hST i) (M i)) K)
    (hkeepR:Q\K.comap Sum.inl≤Q')
    (hkeepP:ordinaryPhysicalGraph Q H\K≤ordinaryPhysicalGraph Q' H')
    (hdis:∀a b:J⊕I,a≠b→Disjoint
      (Sum.elim (fun j=>(localOrdinaryFactorGraph (D j)).map (Function.Embedding.inl:V↪V⊕U))
        (fun i=>endpointFactorGraph (hST i) (M i)) a)
      (Sum.elim (fun j=>(localOrdinaryFactorGraph (D j)).map (Function.Embedding.inl:V↪V⊕U))
        (fun i=>endpointFactorGraph (hST i) (M i)) b))
    (limit:ℝ) (hdeg:∀w:V⊕U,
      ((⨆k:J⊕I,Sum.elim (fun j=>(localOrdinaryFactorGraph (D j)).map (Function.Embedding.inl:V↪V⊕U))
        (fun i=>endpointFactorGraph (hST i) (M i)) k).degree w:ℝ)≤limit):
    ∃C:OrdinaryTriangleSelectedFactors Q' F H' A B T Y hAB limit,
      (∀j,Disjoint ((localOrdinaryFactorGraph (C.hub j)).map (Function.Embedding.inl:V↪V⊕U)) K) ∧
      (∀i,Disjoint (endpointFactorGraph (hAB i) (C.row i)) K):=by
  have hexD (j:J):∃D':Finset (LocalOrdinaryCycle Q' F (T j) 3),
      ((∀C∈D',∀C'∈D',C≠C'→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices C')) ↔
        (∀C∈D j,∀C'∈D j,C≠C'→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices C'))) ∧
      D'.biUnion localOrdinaryVertices=(D j).biUnion localOrdinaryVertices ∧
      localOrdinaryFactorGraph D'=localOrdinaryFactorGraph (D j):=by
    apply local_ordinary_factor_transfer_to_host
    exact local_ordinary_factor_graph_survives_physical_deletion Q Q' F K (T j) 3 (D j) (hDavoid j) hkeepR
  have hexM (i:I):∃M':Finset (EndpointTriangle (ordinaryPhysicalGraph Q' H') (ordinaryPhysicalGraph F (fun _ _=>False))
      ((A i).image Sum.inl) ((B i).image Sum.inr)),
      ((∀C∈M',∀C'∈M',C≠C'→Disjoint (endpointTriangleVertices C) (endpointTriangleVertices C')) ↔
        (∀C∈M i,∀C'∈M i,C≠C'→Disjoint (endpointTriangleVertices C) (endpointTriangleVertices C'))) ∧
      M'.biUnion endpointTriangleVertices=(M i).biUnion endpointTriangleVertices ∧
      endpointFactorGraph (hAB i) M'=endpointFactorGraph (hST i) (M i):=by
    apply endpoint_factor_actual_host
    · exact hA i
    · exact hB i
    · rw [(hM i).2]
    · exact endpoint_factor_graph_survives_deletion (ordinaryPhysicalGraph Q H) (ordinaryPhysicalGraph Q' H')
        (ordinaryPhysicalGraph F (fun _ _=>False)) K (S₀ i) (T₀ i) (hST i) (M i) (hMavoid i) hkeepP
  let D':=fun j=>Classical.choose (hexD j)
  let M':=fun i=>Classical.choose (hexM i)
  have hD' (j:J):=(Classical.choose_spec (hexD j))
  have hM' (i:I):=(Classical.choose_spec (hexM i))
  have hDvalid:∀j,(∀C∈D' j,∀C'∈D' j,C≠C'→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices C')) ∧
      (D' j).biUnion localOrdinaryVertices=Y j:=by
    intro j;exact ⟨(hD' j).1.mpr (hD j).1,(hD' j).2.1.trans (hD j).2⟩
  have hMvalid:∀i,(∀C∈M' i,∀C'∈M' i,C≠C'→Disjoint (endpointTriangleVertices C) (endpointTriangleVertices C')) ∧
      (M' i).biUnion endpointTriangleVertices=(A i).image Sum.inl∪(B i).image Sum.inr:=by
    intro i;exact ⟨(hM' i).1.mpr (hM i).1,(hM' i).2.1.trans (hM i).2⟩
  let G:=fun k:J⊕I=>Sum.elim (fun j=>(localOrdinaryFactorGraph (D j)).map (Function.Embedding.inl:V↪V⊕U))
    (fun i=>endpointFactorGraph (hST i) (M i)) k
  let G':=fun k:J⊕I=>Sum.elim (fun j=>(localOrdinaryFactorGraph (D' j)).map (Function.Embedding.inl:V↪V⊕U))
    (fun i=>endpointFactorGraph (hAB i) (M' i)) k
  have hG (k:J⊕I):G' k=G k:=by
    cases k with
    | inl j =>
      change (localOrdinaryFactorGraph (D' j)).map _ =
        (localOrdinaryFactorGraph (D j)).map _
      exact congrArg (fun G : SimpleGraph V => G.map (Function.Embedding.inl : V ↪ V ⊕ U)) ((hD' j).2.2)
    | inr i =>
      change endpointFactorGraph (hAB i) (M' i) = endpointFactorGraph (hST i) (M i)
      exact (hM' i).2.2
  have hdis':∀a b:J⊕I,a≠b→Disjoint (G' a) (G' b):=by
    intro a b hab;rw [hG a,hG b];exact hdis a b hab
  have heq:(⨆k,G' k)=⨆k,G k:=iSup_congr hG
  have hdeg':∀w:V⊕U,((⨆k,G' k).degree w:ℝ)≤limit:=by
    intro w;rw [heq];convert hdeg w using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  apply ordinary_triangle_selected_factors_from_mixed_with_avoid Q' F H' A B T Y hAB D' M' hDvalid hMvalid hdis' limit hdeg' K
  · intro j
    rw [(hD' j).2.2]
    exact hDavoid j
  · intro i
    rw [(hM' i).2.2]
    exact hMavoid i
end Oberwolfach
