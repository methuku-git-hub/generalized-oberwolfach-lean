module

public import Oberwolfach.PrescribedBadEdgeAssignments

@[expose] public section
/-! Each physical bad edge can be oriented in the supplied target digraph
whenever the target contains one of its two directions. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V] [Nonempty V]

theorem assigned_edge_orientation (G:SimpleGraph V) (D:V→V→Prop)
    (hD:∀x y,G.Adj x y→D x y ∨ D y x):
    ∃ orient:Sym2 V→V×V,∀e∈G.edgeFinset,
      prescribedArcPhysical (orient e)=e ∧ D (orient e).1 (orient e).2 := by
  have hex:∀e∈G.edgeFinset,∃a:V×V,prescribedArcPhysical a=e ∧ D a.1 a.2:=by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hxy:G.Adj x y:=SimpleGraph.mem_edgeFinset.mp he
      rcases hD x y hxy with h|h
      · exact ⟨(x,y),rfl,h⟩
      · exact ⟨(y,x),by simp [prescribedArcPhysical,Sym2.eq_swap],h⟩
  let v:V:=Classical.choice inferInstance
  let orient:Sym2 V→V×V:=fun e=>if he:e∈G.edgeFinset then Classical.choose (hex e he) else (v,v)
  refine ⟨orient,?_⟩
  intro e he
  dsimp only [orient]
  rw [dif_pos he]
  exact Classical.choose_spec (hex e he)
end Oberwolfach
