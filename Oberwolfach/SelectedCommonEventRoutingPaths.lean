module

public import Oberwolfach.SelectedClassRoutingPaths
public import Oberwolfach.MarkedProtectedActiveReferenceStatistics

@[expose] public section
/-! Discharge the routing-path supply from the selected two-path test already
present in the common event and the class-graph edit bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem selected_common_event_routing_paths
    {V:Type} [Fintype V] [LinearOrder V] (P S:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:Sym2 V→Fin 6×Bool) (p err b β:ℝ) (hb:0≤b)
    (hlost:∀v,((Finset.univ.filter (fun w=>
      (rawSelectedPhysicalRelation P π d ω v w ∨ rawSelectedPhysicalRelation P π d ω w v) ∧ ¬S.Adj v w)).card:ℝ)≤b)
    (htest:∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-err≤
      ((Finset.univ.filter (fun z=>
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω e)) false x z ∧
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω e)) false z y)).card:ℝ))
    (hmargin:∀x y,x≠y→β*Fintype.card V+2*b≤
      ((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-err):
    ∀x y,x≠y→β*Fintype.card V≤
      ((Finset.univ.filter (fun z=>0<sampledOrientation S (fun e=>(ω e).2) x z ∧
        0<sampledOrientation S (fun e=>(ω e).2) z y ∧ S.Adj x z ∧ S.Adj z y)).card:ℝ):=by
  apply selected_class_routing_paths P S π d ω b β hb hlost
  intro x y hxy
  have hh:=htest x y hxy
  simp only [markedPhysicalRim_pos_iff_one] at hh
  apply (hmargin x y hxy).trans
  convert hh using 1 <;> congr 5 <;> first | rfl | exact Subsingleton.elim _ _
end Oberwolfach
