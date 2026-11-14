module

public import Oberwolfach.OrdinaryBoundaryGraph
public import Oberwolfach.MixedFreshPairingParentInsideRoots
public import Oberwolfach.EndpointPairingHostTransfer
public import Oberwolfach.OrdinaryLocalFactorHostTransfer

@[expose] public section
/-! Selected general-length hub factors and endpoint pairings on the actual
    edited host, retaining their joint physical disjointness and degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I J:Type} [Fintype V] [Fintype U] [Fintype I] [Fintype J]
  [DecidableEq V] [DecidableEq U] [DecidableEq I] [DecidableEq J]

structure OrdinaryPairingSelectedFactors (m:ℕ) (Q F:SimpleGraph V) (H:V→U→Prop)
    (A:I→Finset V) (B:I→Finset U) (T Y:J→Finset V) (limit:ℝ) where
  hub:∀j,Finset (LocalOrdinaryCycle Q F (T j) (m+1))
  hub_disjoint:∀j,∀C∈hub j,∀C'∈hub j,C≠C'→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices C')
  hub_cover:∀j,(hub j).biUnion localOrdinaryVertices=Y j
  row:∀i,EndpointPairing (ordinaryPhysicalGraph Q H) (ordinaryPhysicalGraph F (fun _ _=>False))
    ((A i).image Sum.inl) ((B i).image Sum.inr)
  cross:∀i j:J⊕I,i≠j→Disjoint
    (Sum.elim (fun j=>(localOrdinaryFactorGraph (hub j)).map (Function.Embedding.inl:V↪V⊕U))
      (fun i=>(row i).graph) i)
    (Sum.elim (fun j=>(localOrdinaryFactorGraph (hub j)).map (Function.Embedding.inl:V↪V⊕U))
      (fun i=>(row i).graph) j)
  inner_degree:∀w:V⊕U,((⨆i:J⊕I,Sum.elim
    (fun j=>(localOrdinaryFactorGraph (hub j)).map (Function.Embedding.inl:V↪V⊕U))
    (fun i=>(row i).graph) i).degree w:ℝ)≤limit
end Oberwolfach
