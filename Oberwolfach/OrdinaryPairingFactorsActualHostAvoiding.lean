module

public import Oberwolfach.OrdinaryPairingSelectedFactorsAvoiding
public import Oberwolfach.OrdinaryLocalFactorAvoidedHost

@[expose] public section
/-! Transfer jointly selected general-length hub factors and endpoint
    pairings across the actual later physical deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I J:Type} [Fintype V] [Fintype U] [Fintype I] [Fintype J]
  [DecidableEq V] [DecidableEq U] [DecidableEq I] [DecidableEq J]

theorem ordinary_pairing_factors_actual_host_avoiding
    (m:ℕ) (Q Q' F:SimpleGraph V) (H H':V→U→Prop) (K:SimpleGraph (V⊕U))
    (A:I→Finset V) (B:I→Finset U) (T Y:J→Finset V)
    (D:∀j,Finset (LocalOrdinaryCycle Q F (T j) (m+1)))
    (M:∀i,EndpointPairing (ordinaryPhysicalGraph Q H) (ordinaryPhysicalGraph F (fun _ _=>False))
      ((A i).image Sum.inl) ((B i).image Sum.inr))
    (hD:∀j,(∀C∈D j,∀C'∈D j,C≠C'→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices C')) ∧
      (D j).biUnion localOrdinaryVertices=Y j)
    (hDavoid:∀j,Disjoint ((localOrdinaryFactorGraph (D j)).map (Function.Embedding.inl:V↪V⊕U)) K)
    (hMavoid:∀i,Disjoint (M i).graph K)
    (hkeepR:Q\K.comap Sum.inl≤Q') (hkeepP:ordinaryPhysicalGraph Q H\K≤ordinaryPhysicalGraph Q' H')
    (hdis:∀a b:J⊕I,a≠b→Disjoint
      (Sum.elim (fun j=>(localOrdinaryFactorGraph (D j)).map (Function.Embedding.inl:V↪V⊕U)) (fun i=>(M i).graph) a)
      (Sum.elim (fun j=>(localOrdinaryFactorGraph (D j)).map (Function.Embedding.inl:V↪V⊕U)) (fun i=>(M i).graph) b))
    (limit:ℝ) (hdeg:∀w:V⊕U,((⨆k:J⊕I,Sum.elim
      (fun j=>(localOrdinaryFactorGraph (D j)).map (Function.Embedding.inl:V↪V⊕U)) (fun i=>(M i).graph) k).degree w:ℝ)≤limit):
    Nonempty (OrdinaryPairingSelectedFactorsAvoiding m Q' F H' A B T Y limit K):=by
  have hexD (j:J):∃D':Finset (LocalOrdinaryCycle Q' F (T j) (m+1)),
      ((∀C∈D',∀C'∈D',C≠C'→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices C')) ↔
        (∀C∈D j,∀C'∈D j,C≠C'→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices C'))) ∧
      D'.biUnion localOrdinaryVertices=(D j).biUnion localOrdinaryVertices ∧
      localOrdinaryFactorGraph D'=localOrdinaryFactorGraph (D j):=by
    apply local_ordinary_factor_transfer_to_host
    exact local_ordinary_factor_graph_survives_physical_deletion Q Q' F K (T j) (m+1) (D j) (hDavoid j) hkeepR
  let D':=fun j=>Classical.choose (hexD j)
  have hD' (j:J):=Classical.choose_spec (hexD j)
  have hMsub (i:I):(M i).graph≤ordinaryPhysicalGraph Q' H':=
    endpoint_pairing_survives_deletion (ordinaryPhysicalGraph Q H) (ordinaryPhysicalGraph Q' H')
      (ordinaryPhysicalGraph F (fun _ _=>False)) K _ _ (M i) (hMavoid i) hkeepP
  let M':=fun i=>endpointPairingToHost (ordinaryPhysicalGraph Q H) (ordinaryPhysicalGraph Q' H')
    (ordinaryPhysicalGraph F (fun _ _=>False)) _ _ (M i) (hMsub i)
  let G:=fun k:J⊕I=>Sum.elim (fun j=>(localOrdinaryFactorGraph (D j)).map (Function.Embedding.inl:V↪V⊕U))
    (fun i=>(M i).graph) k
  let G':=fun k:J⊕I=>Sum.elim (fun j=>(localOrdinaryFactorGraph (D' j)).map (Function.Embedding.inl:V↪V⊕U))
    (fun i=>(M' i).graph) k
  have hG (k:J⊕I):G' k=G k:=by
    cases k with
    | inl j =>
      change (localOrdinaryFactorGraph (D' j)).map _=(localOrdinaryFactorGraph (D j)).map _
      exact congrArg (fun G:SimpleGraph V=>G.map (Function.Embedding.inl:V↪V⊕U)) ((hD' j).2.2)
    | inr i =>
      change (M' i).graph=(M i).graph
      exact endpoint_pairing_to_host_graph _ _ _ _ _ (M i) (hMsub i)
  have hdis':∀a b:J⊕I,a≠b→Disjoint (G' a) (G' b):=by
    intro a b hab;rw [hG a,hG b];exact hdis a b hab
  have heq:(⨆k,G' k)=⨆k,G k:=iSup_congr hG
  have hdeg':∀w:V⊕U,((⨆k,G' k).degree w:ℝ)≤limit:=by
    intro w;rw [heq];convert hdeg w using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  let selected:OrdinaryPairingSelectedFactors m Q' F H' A B T Y limit:=
    ⟨D',fun j=>(hD' j).1.mpr (hD j).1,fun j=>(hD' j).2.1.trans (hD j).2,M',hdis',hdeg'⟩
  refine ⟨⟨selected,?_⟩⟩
  intro i
  change Disjoint (G' i) K
  rw [hG i]
  cases i with
  | inl j=>exact hDavoid j
  | inr i=>exact hMavoid i
end Oberwolfach
