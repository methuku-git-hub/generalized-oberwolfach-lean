module

public import Oberwolfach.OrdinaryInducedIntersectionCards

@[expose] public section
/-! Transport an induced cross-balance estimate back to the parent vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_cross_balance_induced_reverse
    (G:SimpleGraph V) (H:V→U→Prop) (A I:Finset V) (B J:Finset U) (hI:I⊆A) (hJ:J⊆B) (b:ℝ)
    (hbal:let Ilocal:Finset A:=Finset.univ.filter (fun x:A=>x.val∈I);
      let Jlocal:Finset B:=Finset.univ.filter (fun u:B=>u.val∈J);
      ∀v:A,v∉Ilocal→|((((G.induce (A:Set V)).neighborFinset v)∩Ilocal).card:ℝ)-
        2*(Jlocal.filter (fun u:B=>H v.val u.val)).card|≤b):
    ∀v∈A,v∉I→|((G.neighborFinset v∩I).card:ℝ)-2*(J.filter (H v)).card|≤b :=by
  intro v hv hv'
  let x:A:=⟨v,hv⟩
  let Ilocal:Finset A:=Finset.univ.filter (fun x:A=>x.val∈I)
  let Jlocal:Finset B:=Finset.univ.filter (fun u:B=>u.val∈J)
  have hx:x∉Ilocal:=by simpa [Ilocal,x] using hv'
  have hII:I∩A=I:=Finset.inter_eq_left.mpr hI
  have hJB:J∩B=J:=Finset.inter_eq_left.mpr hJ
  have hN:(((G.induce (A:Set V)).neighborFinset x)∩Ilocal).card=(G.neighborFinset v∩I).card:=by
    have hh:=ordinary_induced_neighbor_intersection_card G A I x
    rw [hII] at hh
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hS:(Jlocal.filter (fun u:B=>H v u.val)).card=(J.filter (H v)).card:=by
    have hfilter:Jlocal.filter (fun u:B=>H v u.val)=
        Finset.univ.filter (fun u:B=>H v u.val∧u.val∈J):=by ext u;simp [Jlocal,and_comm]
    rw [hfilter]
    have hh:=ordinary_induced_spoke_intersection_card H B J v
    rw [hJB] at hh
    have he:(Finset.univ.filter (H v))∩J=J.filter (H v):=by ext u;simp [and_comm]
    rw [he] at hh
    exact hh
  have hh:=hbal x hx
  rw [hN,hS] at hh
  convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
