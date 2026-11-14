module

public import Oberwolfach.LongPreparationPhysicalStates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]

theorem long_selected_close_edge_has_marked_direction
    (G:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (x y:V) (hSel:(longSelectedPhysicalGraph G π d ω).Adj x y)
    (hClose:PermutationClose π (3*d) x y):
    markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω (Sum.inl e))) true x (π.symm y)=1 ∨
    markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω (Sum.inl e))) true y (π.symm x)=1:=by
  let raw:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedMarkedCollapse e (ω e)
  change x≠y ∧ ({x,y}:Finset V)∈
    (Finset.univ.image (markedPhysicalEdge
      (fun e:MarkedSampleArc G π (3*d) (fun e=>raw (Sum.inl e)) false=>e.val.1)
      (fun e:MarkedSampleArc G π (3*d) (fun e=>raw (Sum.inl e)) false=>e.val.2)
      (fun e:MarkedSampleArc G π (3*d) (fun e=>raw (Sum.inl e)) true=>e.val.1)
      (fun e:MarkedSampleArc G π (3*d) (fun e=>raw (Sum.inl e)) true=>e.val.2) π)) at hSel
  obtain ⟨a,_,ha⟩:=Finset.mem_image.mp hSel.2
  have hpair {a b c e:V} (hh:({a,b}:Finset V)={c,e}):a=c ∧ b=e ∨ a=e ∧ b=c:=by
    apply Set.pair_eq_pair_iff.mp
    simpa only [Finset.coe_pair] using congrArg (fun S:Finset V=>(S:Set V)) hh
  cases a with
  | inl e=>
    have hfar:=((markedPhysicalRim_eq_one_iff G π (3*d) (fun e=>raw (Sum.inl e)) false e.val.1 e.val.2).mp e.property).1
    rcases hpair (by simpa [markedPhysicalEdge] using ha) with ⟨h1,h2⟩|⟨h1,h2⟩
    · exact False.elim (hfar (by simpa only [h1,h2] using hClose))
    · exact False.elim (hfar (by simpa only [h1,h2] using (permutationClose_symm π (3*d) x y).mp hClose))
  | inr e=>
    rcases hpair (by simpa [markedPhysicalEdge] using ha) with ⟨h1,h2⟩|⟨h1,h2⟩
    · left
      have hr:=e.property
      change markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω (Sum.inl e))) true e.val.1 e.val.2=1 at hr
      rw [h1] at hr
      have hh:e.val.2=π.symm y:=by apply π.injective;simpa using h2
      simpa only [hh] using hr
    · right
      have hr:=e.property
      change markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω (Sum.inl e))) true e.val.1 e.val.2=1 at hr
      rw [h1] at hr
      have hh:e.val.2=π.symm x:=by apply π.injective;simpa using h2
      simpa only [hh] using hr
end Oberwolfach
