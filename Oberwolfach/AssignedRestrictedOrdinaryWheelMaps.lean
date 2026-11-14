module

public import Oberwolfach.OrdinaryComponentWheelFamilyMaps
public import Oberwolfach.OrdinaryRestrictedWheelDisjointness

@[expose] public section
/-! Maps for assigned components of the same hub are vertex-disjoint when
their sampled typed resource sets form a matching. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U A X:Type} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]

theorem assigned_restricted_ordinary_wheel_maps
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (π:Equiv.Perm (Fin n)) (b:ℕ) (r:A→ℕ)
    (e:X↪(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (Q:∀a,RestrictedResource (fun W:OrderedOrdinaryWheel (U:=U) π b (r a)=>
      (orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding) e)
    (C:∀a,(F (Q a).val.2).ConnectedComponent)
    (hsize:∀a,Fintype.card (C a)=r a)
    (hdis:∀a a',a≠a'→(Q a).val.2=(Q a').val.2→
      Disjoint (restrictedResourceSet (fun W:OrderedOrdinaryWheel (U:=U) π b (r a)=>
        (orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding) e (Q a))
        (restrictedResourceSet (fun W:OrderedOrdinaryWheel (U:=U) π b (r a')=>
        (orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding) e (Q a'))):
    ∃ f:∀a,(C a)↪Fin n,
      (∀a x,∃i:Fin (r a),f a x=(Q a).val.1.val i) ∧
      (∀a,∀i:Fin (r a),∃x:C a,f a x=(Q a).val.1.val i) ∧
      (∀a x y,(C a).toSimpleGraph.Adj x y→
        ∃i:Fin (r a),(f a x=(Q a).val.1.val i ∧ f a y=(Q a).val.1.val (cycleNext i)) ∨
          (f a y=(Q a).val.1.val i ∧ f a x=(Q a).val.1.val (cycleNext i))) ∧
      (∀a x,Sum.inr (f a x,(Q a).val.2)∈orderedOrdinaryResources (Q a).val) ∧
      (∀a a',a≠a'→(Q a).val.2=(Q a').val.2→
        Disjoint (Finset.univ.image (f a)) (Finset.univ.image (f a'))) :=by
  apply ordinary_component_wheel_family_maps F hF π b (fun a=>(Q a).val.2) r
    (fun a=>(Q a).val) C hsize (fun _=>rfl)
  intro a a' hne heq
  apply ordinary_restricted_wheels_original_resources_disjoint π b (r a) (r a') e (Q a) (Q a')
  convert hdis a a' hne heq using 1 <;> congr 3 <;> exact Subsingleton.elim _ _
end Oberwolfach
