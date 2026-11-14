module

public import Oberwolfach.PrescribedTargetPathChains
public import Oberwolfach.PrescribedPathDirectedEdges

@[expose] public section
/-! A realized cycle gives every target arc in its source order. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X V:Type} [Fintype V] [DecidableEq X] [DecidableEq V]

theorem prescribed_cycle_target_arcs (g:X→V) (D:V→V→Prop) (F:SimpleGraph V) (a:X) (xs:List X)
    (h:DirectedPathThrough D F (g a) (g a) (xs.map g)):
    ∀ e∈prescribedDirectedPathEdges ((a::xs)++[a]),D (g e.1) (g e.2) := by
  have hc:=prescribed_target_two_chain g D F a a xs h
  have hc':List.IsChain (fun x y=>D (g x) (g y)) ((a::xs)++[a]):=(List.isChain_map g).mp hc
  exact (prescribed_directed_edges_chain _ _).mp hc'
end Oberwolfach
