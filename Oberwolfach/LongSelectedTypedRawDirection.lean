module

public import Oberwolfach.LongDualResidualEligibility
public import Oberwolfach.MarkedExpandedPhysicalLaw
public import Oberwolfach.RandomColourCuts

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [LinearOrder V]
local instance selectedTypedRawDecEq : DecidableEq V := Classical.decEq V

theorem long_selected_ordinary_raw_direction
    (G:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (ω:Sym2 V→Fin 6×Bool) (x y:V)
    (h:markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω e)) false x y=1):
    sampledColourOrientation G ω 0 x y=1 ∧ longOrdinaryArcEligible π d (x,y):=by
  have hh:=(markedPhysicalRim_eq_one_iff G π (3*d) _ false x y).mp h
  refine ⟨?_,hh.1⟩
  have hs:=hh.2.2
  rcases hω:ω s(x,y) with ⟨state,bit⟩
  fin_cases state <;> simp_all [markedExpandedPhysicalCollapse,sampledColourOrientation]

theorem long_selected_marked_raw_direction
    (G:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (ω:Sym2 V→Fin 6×Bool) (x y:V)
    (h:markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω e)) true x (π.symm y)=1):
    sampledColourOrientation G ω 1 x y=1 ∧ longMarkedArcEligible π d (x,y):=by
  have hh:=(markedPhysicalRim_eq_one_iff G π (3*d) _ true x (π.symm y)).mp h
  refine ⟨?_,hh.1⟩
  have hG:G.Adj x y:=by simpa only [Equiv.apply_symm_apply,ite_true] using hh.2.1
  have hs:markedExpandedPhysicalCollapse (ω s(x,y))=some (true,orientationBit x y):=by
    simpa only [Equiv.apply_symm_apply,ite_true] using hh.2.2
  rcases hω:ω s(x,y) with ⟨state,bit⟩
  fin_cases state <;> simp_all [markedExpandedPhysicalCollapse,sampledColourOrientation]
end Oberwolfach
