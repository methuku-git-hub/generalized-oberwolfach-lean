module

public import Oberwolfach.OrdinaryInducedIntersectionCards

@[expose] public section
/-! Transfer ambient cross-balance to an induced parent pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_cross_balance_induced_transport
    (G:SimpleGraph V) (H:V→U→Prop) (A I:Finset V) (B J:Finset U) (hI:I⊆A) (hJ:J⊆B) (b:ℝ)
    (hbal:∀v∉I,|((G.neighborFinset v∩I).card:ℝ)-2*(J.filter (H v)).card|≤b):
    let Ilocal:Finset A:=Finset.univ.filter (fun x:A=>x.val∈I);
    let Jlocal:Finset B:=Finset.univ.filter (fun u:B=>u.val∈J);
    ∀v:A,v∉Ilocal→|((((G.induce (A:Set V)).neighborFinset v)∩Ilocal).card:ℝ)-
      2*(Jlocal.filter (fun u:B=>H v.val u.val)).card|≤b :=by
  intro Ilocal Jlocal v hv
  have hv':v.val∉I:=by
    intro hh
    apply hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩
  have hII:I∩A=I:=Finset.inter_eq_left.mpr hI
  have hJB:J∩B=J:=Finset.inter_eq_left.mpr hJ
  have hN:(((G.induce (A:Set V)).neighborFinset v)∩Ilocal).card=(G.neighborFinset v.val∩I).card:=by
    have hh:=ordinary_induced_neighbor_intersection_card G A I v
    rw [hII] at hh
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hS:(Jlocal.filter (fun u:B=>H v.val u.val)).card=(J.filter (H v.val)).card:=by
    have hfilter:Jlocal.filter (fun u:B=>H v.val u.val)=
        Finset.univ.filter (fun u:B=>H v.val u.val∧u.val∈J):=by ext u;simp [Jlocal,and_comm]
    rw [hfilter]
    have hh:=ordinary_induced_spoke_intersection_card H B J v.val
    rw [hJB] at hh
    have he:(Finset.univ.filter (H v.val))∩J=J.filter (H v.val):=by ext u;simp [and_comm]
    rw [he] at hh
    exact hh
  rw [hN,hS]
  convert hbal v.val hv' using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
