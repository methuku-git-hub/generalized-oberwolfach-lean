module

public import Oberwolfach.OrdinaryPackingCleanupData

@[expose] public section
/-! Name the actual post-packing graph and retain its physical certificate
in a compact record for subsequent cleanup and factor selection. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 2048
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryPackingUsedGraph (Q F:SimpleGraph V) (H:V→U→Prop)
    (X:Finset V) (Z:Finset U) (R:SimpleGraph (V⊕U)) (r:ℕ) (t:ℝ)
    (M:OrdinaryUnreservedPackingData Q F H X Z R r t):SimpleGraph (V⊕U):=
  ordinaryPhysicalGraph (ordinaryWheelRimGraph M.wheels) (ordinaryPackingSpokes M.wheels)

def ordinaryPackingPostRim (Q F:SimpleGraph V) (H:V→U→Prop)
    (X:Finset V) (Z:Finset U) (R:SimpleGraph (V⊕U)) (r:ℕ) (t:ℝ)
    (M:OrdinaryUnreservedPackingData Q F H X Z R r t):SimpleGraph V:=Q\ordinaryWheelRimGraph M.wheels

def ordinaryPackingPostSpokes (Q F:SimpleGraph V) (H:V→U→Prop)
    (X:Finset V) (Z:Finset U) (R:SimpleGraph (V⊕U)) (r:ℕ) (t:ℝ)
    (M:OrdinaryUnreservedPackingData Q F H X Z R r t):V→U→Prop:=fun v u=>H v u∧¬ordinaryPackingSpokes M.wheels v u

structure OrdinaryPackingPostFacts (Q F:SimpleGraph V) (H:V→U→Prop)
    (X:Finset V) (Z:Finset U) (R:SimpleGraph (V⊕U)) (r:ℕ) (t:ℝ)
    (M:OrdinaryUnreservedPackingData Q F H X Z R r t):Prop where
  inner_avoided:Disjoint (ordinaryPackingUsedGraph Q F H X Z R r t M)
    (spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z))
  reserve_avoided:Disjoint (ordinaryPackingUsedGraph Q F H X Z R r t M) R
  unreserved_leftover:∀w,((((ordinaryPhysicalGraph Q H\spanningRestriction (ordinaryPhysicalGraph Q H)
    (ordinaryInnerVertices X Z))\R)\ordinaryPackingUsedGraph Q F H X Z R r t M).degree w:ℝ)≤t
  exact_remainder:ordinaryPhysicalGraph (ordinaryPackingPostRim Q F H X Z R r t M)
    (ordinaryPackingPostSpokes Q F H X Z R r t M)=ordinaryPhysicalGraph Q H\ordinaryPackingUsedGraph Q F H X Z R r t M
  balance:∀v,(ordinaryPackingPostRim Q F H X Z R r t M).degree v=
    2*(Finset.univ.filter (ordinaryPackingPostSpokes Q F H X Z R r t M v)).card
  divisible:∀u,r∣(Finset.univ.filter (fun v=>ordinaryPackingPostSpokes Q F H X Z R r t M v u)).card

theorem ordinary_packing_post_facts (Q F:SimpleGraph V) (H:V→U→Prop)
    (X:Finset V) (Z:Finset U) (R:SimpleGraph (V⊕U)) (r:ℕ) (t:ℝ)
    (M:OrdinaryUnreservedPackingData Q F H X Z R r t)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card):
    OrdinaryPackingPostFacts Q F H X Z R r t M:=by
  have hc:=ordinary_unreserved_packing_certificate Q F H X Z R r M.wheels M.disjoint t M.leftover hbal hdiv
  refine ⟨hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.1,?_,?_⟩
  · convert hc.2.2.2.2.1 using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · convert hc.2.2.2.2.2 using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
