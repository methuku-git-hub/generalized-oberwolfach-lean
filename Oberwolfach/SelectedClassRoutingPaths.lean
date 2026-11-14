module

public import Oberwolfach.SelectedClassOrientationLoss

@[expose] public section
/-! The common selected two-path event supplies the routing paths after the
sampled class is changed by bounded degree. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem selected_class_routing_paths
    {V:Type} [Fintype V] [LinearOrder V] (P S:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:Sym2 V→Fin 6×Bool) (b β:ℝ) (hb:0≤b)
    (hlost:∀v,((Finset.univ.filter (fun w=>
      (rawSelectedPhysicalRelation P π d ω v w ∨ rawSelectedPhysicalRelation P π d ω w v) ∧ ¬S.Adj v w)).card:ℝ)≤b)
    (hsupply:∀x y,x≠y→β*Fintype.card V+2*b≤
      ((Finset.univ.filter (fun z=>rawSelectedPhysicalRelation P π d ω x z ∧
        rawSelectedPhysicalRelation P π d ω z y)).card:ℝ)):
    ∀x y,x≠y→β*Fintype.card V≤
      ((Finset.univ.filter (fun z=>0<sampledOrientation S (fun e=>(ω e).2) x z ∧
        0<sampledOrientation S (fun e=>(ω e).2) z y ∧ S.Adj x z ∧ S.Adj z y)).card:ℝ):=by
  intro x y hxy
  have h:=selected_class_two_paths_after_edits P S π d ω b hb hlost x y
  linarith [hsupply x y hxy]
end Oberwolfach
