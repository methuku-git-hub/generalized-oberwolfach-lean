module

public import Oberwolfach.PrescribedPathScheduleChain

@[expose] public section
/-! The realized directed paths give the target arcs in the original source
order, including when the path was embedded from its right endpoint. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X V:Type} [Fintype V] [DecidableEq X] [DecidableEq V]

theorem prescribed_target_left_chain (g:X→V) (D:V→V→Prop) (F:SimpleGraph V) (a:X) (as:List X)
    (h:DirectedPathFrom D F true (g a) (as.map g)):
    List.IsChain D ((a::as).map g) := by
  have hc:List.IsChain (fun x y=>D x y ∧ ¬F.Adj x y) ((a::as).map g):=by
    simpa using (prescribed_path_from_chain D F true (as.map g) (g a)).mp h
  exact hc.imp (by intro x y hxy;exact hxy.1)

theorem prescribed_target_two_chain (g:X→V) (D:V→V→Prop) (F:SimpleGraph V) (a b:X) (as:List X)
    (h:DirectedPathThrough D F (g a) (g b) (as.map g)):
    List.IsChain D ((a::as++[b]).map g) := by
  have hc:List.IsChain (fun x y=>D x y ∧ ¬F.Adj x y) ((a::as++[b]).map g):=by
    simpa using (prescribed_path_through_chain D F (as.map g) (g a) (g b)).mp h
  exact hc.imp (by intro x y hxy;exact hxy.1)

theorem prescribed_target_free_chain (g:X→V) (D:V→V→Prop) (F:SimpleGraph V) (as:List X)
    (h:DirectedNonemptyPath D F true (as.map g)):
    List.IsChain D (as.map g) := by
  cases as with
  | nil => contradiction
  | cons a xs => exact prescribed_target_left_chain g D F a xs h

theorem prescribed_target_right_chain (g:X→V) (D:V→V→Prop) (F:SimpleGraph V) (b:X) (as:List X)
    (h:DirectedPathFrom D F false (g b) (as.reverse.map g)):
    List.IsChain D ((as++[b]).map g) := by
  have hc:= (prescribed_path_from_chain D F false (as.reverse.map g) (g b)).mp h
  have hr:List.IsChain (fun x y=>D x y ∧ ¬F.Adj y x) (g b::as.reverse.map g).reverse:=by
    apply List.isChain_reverse.mpr
    simpa using hc
  have hr':List.IsChain (fun x y=>D x y ∧ ¬F.Adj y x) ((as++[b]).map g):=by
    simpa [List.reverse_cons,List.reverse_append] using hr
  exact hr'.imp (by intro x y hxy;exact hxy.1)
end Oberwolfach
