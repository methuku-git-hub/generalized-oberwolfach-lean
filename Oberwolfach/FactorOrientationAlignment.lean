module

public import Oberwolfach.FactorOrientationOrbit
public import Oberwolfach.DirectedCycleOrientationPropagation

@[expose] public section
/-! A single consistently oriented edge per factor component determines the
orientation of every edge in that component. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_orientation_aligns_from_component_edges
    {X:Type*} [Fintype X] [DecidableEq X] (G:SimpleGraph X) (hG:G.IsRegularOfDegree 2)
    (e:∀C:G.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (D:X→X→Prop)
    (hcover:∀x y,G.Adj x y→D x y ∨ D y x)
    (hin:∀x y z,D y x→D z x→y=z)
    (hbase:∀C:G.ConnectedComponent,∃a:C,D a.val (factorCycleOrientation G e a.val)):
    ∀x,D x (factorCycleOrientation G e x):=by
  intro x
  let C:=G.connectedComponentMk x
  let b:C:=⟨x,(SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl⟩
  obtain ⟨a,ha⟩:=hbase C
  obtain ⟨n,hn⟩:=factor_cycle_orientation_reaches_component G hG e C a b
  have hσcover:∀y,D y (factorCycleOrientation G e y) ∨ D (factorCycleOrientation G e y) y:=
    fun y=>hcover y _ (factor_cycle_orientation_adj G hG e y)
  have hh:=directed_orientation_propagates_on_orbit (factorCycleOrientation G e) D hσcover hin
    (factor_orientation_no_two_cycles G hG e) a.val ha n
  simpa [hn,b] using hh
end Oberwolfach
