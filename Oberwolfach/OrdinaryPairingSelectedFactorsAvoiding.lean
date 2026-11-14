module

public import Oberwolfach.OrdinaryPairingSelectedFactors

@[expose] public section
/-! Retain avoidance of a physical blocker in addition to the selected hub
factors, endpoint pairings, cross-disjointness and degree bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I J:Type} [Fintype V] [Fintype U] [Fintype I] [Fintype J]
  [DecidableEq V] [DecidableEq U] [DecidableEq I] [DecidableEq J]

structure OrdinaryPairingSelectedFactorsAvoiding (m:ℕ) (Q F:SimpleGraph V) (H:V→U→Prop)
    (A:I→Finset V) (B:I→Finset U) (T Y:J→Finset V) (limit:ℝ) (K:SimpleGraph (V⊕U)) where
  selected:OrdinaryPairingSelectedFactors m Q F H A B T Y limit
  avoids:∀i:J⊕I,Disjoint
    (Sum.elim (fun j=>(localOrdinaryFactorGraph (selected.hub j)).map (Function.Embedding.inl:V↪V⊕U))
      (fun i=>(selected.row i).graph) i) K
end Oberwolfach
