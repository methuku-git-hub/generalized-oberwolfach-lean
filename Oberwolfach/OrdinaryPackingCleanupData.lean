module

public import Oberwolfach.OrdinaryUnreservedPackingCertificate
public import Oberwolfach.OrdinaryOutsideCleanupWithMargins

@[expose] public section
/-! Compact data for an unreserved packing and its sparse outside cleanup. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

structure OrdinaryUnreservedPackingData (Q F:SimpleGraph V) (H:V→U→Prop)
    (X:Finset V) (Z:Finset U) (R:SimpleGraph (V⊕U)) (r:ℕ) (t:ℝ) where
  wheels:Finset (OrdinaryWheel (ordinaryUnreservedRim Q X R) F (ordinaryUnreservedSpokes H X Z R) r)
  disjoint:∀A∈wheels,∀B∈wheels,A≠B→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B)
  leftover:∀w:V⊕U,((ordinaryIncidentEdges (ordinaryUnreservedRim Q X R) (ordinaryUnreservedSpokes H X Z R) w\
    wheels.biUnion ordinaryActiveResources).card:ℝ)≤t

structure OrdinaryOutsideCleanupData (Q F:SimpleGraph V) (H:V→U→Prop)
    (X:Finset V) (Z:Finset U) (C:SimpleGraph (V⊕U)) (r:ℕ) (t:ℝ) where
  Nr:ℕ
  Ns:ℕ
  wheels:(Fin Nr⊕Fin Ns)→OrdinaryWheel Q F H r
  disjoint:∀i j,i≠j→Disjoint (ordinaryWheelResources (wheels i)) (ordinaryWheelResources (wheels j))
  decomposition:HasOrdinaryWheelDecomposition (wheelFamilyRim wheels) (wheelFamilySpokes wheels) r
  no_outer_rim:∀v∉X,∀w∉X,¬(Q\wheelFamilyRim wheels).Adj v w
  no_outer_spoke:∀v∉X,∀u∉Z,¬(H v u∧¬wheelFamilySpokes wheels v u)
  degree:∀w:V⊕U,((ordinaryPhysicalGraph (wheelFamilyRim wheels) (wheelFamilySpokes wheels)).degree w:ℝ)≤t
  avoids_prior:Disjoint (ordinaryPhysicalGraph (wheelFamilyRim wheels) (wheelFamilySpokes wheels)) C
end Oberwolfach
