module

public import Oberwolfach.OrdinaryRootCoverData
public import Oberwolfach.OrdinaryCleanupPostFacts

@[expose] public section
/-! Package the three sequential packings before the final boundary finish,
keeping each host as the actual remainder of its predecessor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

structure OrdinaryPackingCleanupRootContext (Q F:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (R:SimpleGraph (V⊕U)) (r:ℕ) (t ν η ell:ℝ) where
  packing:OrdinaryUnreservedPackingData Q F H X Z R r t
  cleanup:OrdinaryOutsideCleanupData
    (ordinaryPackingPostRim Q F H X Z R r t packing) F
    (ordinaryPackingPostSpokes Q F H X Z R r t packing) X Z
    (ordinaryPackingUsedGraph Q F H X Z R r t packing) r ν
  root:OrdinaryRootCoverData
    (ordinaryCleanupPostRim (ordinaryPackingPostRim Q F H X Z R r t packing) F
      (ordinaryPackingPostSpokes Q F H X Z R r t packing) X Z
      (ordinaryPackingUsedGraph Q F H X Z R r t packing) r ν cleanup) F
    (ordinaryCleanupPostSpokes (ordinaryPackingPostRim Q F H X Z R r t packing) F
      (ordinaryPackingPostSpokes Q F H X Z R r t packing) X Z
      (ordinaryPackingUsedGraph Q F H X Z R r t packing) r ν cleanup) X T Z W r η ell

def OrdinaryPackingCleanupRootContext.postRim
    {Q F:SimpleGraph V} {H:V→U→Prop} {X T:Finset V} {Z W:Finset U}
    {R:SimpleGraph (V⊕U)} {r:ℕ} {t ν η ell:ℝ}
    (A:OrdinaryPackingCleanupRootContext Q F H X T Z W R r t ν η ell):SimpleGraph V:=
  (ordinaryCleanupPostRim (ordinaryPackingPostRim Q F H X Z R r t A.packing) F
    (ordinaryPackingPostSpokes Q F H X Z R r t A.packing) X Z
    (ordinaryPackingUsedGraph Q F H X Z R r t A.packing) r ν A.cleanup)\A.root.rim

def OrdinaryPackingCleanupRootContext.postSpokes
    {Q F:SimpleGraph V} {H:V→U→Prop} {X T:Finset V} {Z W:Finset U}
    {R:SimpleGraph (V⊕U)} {r:ℕ} {t ν η ell:ℝ}
    (A:OrdinaryPackingCleanupRootContext Q F H X T Z W R r t ν η ell):V→U→Prop:=
  fun v u=>ordinaryCleanupPostSpokes (ordinaryPackingPostRim Q F H X Z R r t A.packing) F
    (ordinaryPackingPostSpokes Q F H X Z R r t A.packing) X Z
    (ordinaryPackingUsedGraph Q F H X Z R r t A.packing) r ν A.cleanup v u ∧ ¬A.root.spokes v u
end Oberwolfach
