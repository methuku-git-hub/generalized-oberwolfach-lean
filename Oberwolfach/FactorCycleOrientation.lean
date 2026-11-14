module

public import Oberwolfach.FiberwisePermutation
public import Oberwolfach.CyclicCoordinates

@[expose] public section
/-! Assemble chosen cyclic component orders into a global vertex permutation. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def componentFiberEquiv {X:Type*} [Fintype X] [DecidableEq X]
    (G:SimpleGraph X) (C:G.ConnectedComponent):
    {x // G.connectedComponentMk x=C} ≃ C where
  toFun x:=⟨x.val,(SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr x.property⟩
  invFun x:=⟨x.val,(SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp x.property⟩
  left_inv:=by intro x;apply Subtype.ext;rfl
  right_inv:=by intro x;apply Subtype.ext;rfl

def componentFiberCyclePermutation {X:Type*} [Fintype X] [DecidableEq X]
    (G:SimpleGraph X) (C:G.ConnectedComponent)
    (e:SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph):
    Equiv.Perm {x // G.connectedComponentMk x=C} :=
  (componentFiberEquiv G C).trans
    ((e.toEquiv.symm.trans ((finRotate (Fintype.card C)).trans e.toEquiv)).trans (componentFiberEquiv G C).symm)

def factorCycleOrientation {X:Type*} [Fintype X] [DecidableEq X]
    (G:SimpleGraph X) (e:∀C:G.ConnectedComponent,
      SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph):Equiv.Perm X :=
  fiberwisePermutation G.connectedComponentMk (fun C=>componentFiberCyclePermutation G C (e C))

theorem factor_cycle_orientation_preserves_component {X:Type*} [Fintype X] [DecidableEq X]
    (G:SimpleGraph X) (e:∀C:G.ConnectedComponent,
      SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph) (x:X):
    G.connectedComponentMk (factorCycleOrientation G e x)=G.connectedComponentMk x:=
  fiberwise_permutation_preserves G.connectedComponentMk (fun C=>componentFiberCyclePermutation G C (e C)) x

theorem factor_cycle_orientation_on_component {X:Type*} [Fintype X] [DecidableEq X]
    (G:SimpleGraph X) (e:∀C:G.ConnectedComponent,
      SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (C:G.ConnectedComponent) (x:C):
    factorCycleOrientation G e x.val=(e C (finRotate (Fintype.card C) ((e C).symm x))).val:=by
  have h:G.connectedComponentMk x.val=C:=(SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp x.property
  cases x with
  | mk v hv =>
    dsimp only at h
    subst C
    rfl
end Oberwolfach
