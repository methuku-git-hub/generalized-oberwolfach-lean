module

public import Oberwolfach.MarkedPartitionedResidualHost
public import Oberwolfach.MarkedIndegreeFinsetInterface
public import Oberwolfach.MarkedMatrixDivisibility

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [LinearOrder V]
local instance residualDegreesDecEq : DecidableEq V := Classical.decEq V
local instance residualDegreesArc (P:V×V→Prop):DecidableEq {e:V×V // P e}:=Classical.decEq _
local instance residualDegreesArcFinite (P:V×V→Prop):Fintype {e:V×V // P e}:=Fintype.ofFinite _
local instance residualMarkedFinite (P:V×V→Prop) (M:Finset {e:V×V // P e}):Fintype (residualMarkedArc P M):=by
  change Fintype {e:{a:V×V // P a} // e∈M}
  exact Fintype.ofFinite _

theorem partitioned_marked_head_degree
    (P:V×V→Prop) (M:Finset {e:V×V // P e}) (π:Equiv.Perm V) (v:V):
    occurrenceDegree (fun e:residualMarkedArc P M=>π.symm e.val.val.2) v=
      (directedInCount P M (π v):ℝ):=by
  let K:=residualMarkedArc P M
  let A:=M.filter (fun e=>e.val.2=π v)
  let e:{x:K // π.symm x.val.val.2=v} ≃ {x:{a:V×V // P a} // x∈A}:={
    toFun:=fun x=>⟨x.val.val,Finset.mem_filter.mpr ⟨x.val.property,by
      have hh:=congrArg π x.property
      simpa only [Equiv.apply_symm_apply] using hh⟩⟩
    invFun:=fun x=>⟨⟨x.val,(Finset.mem_filter.mp x.property).1⟩,by
      have hh:=(Finset.mem_filter.mp x.property).2
      simpa only [hh,Equiv.symm_apply_apply]⟩
    left_inv:=by intro x;cases x with | mk x hx=>cases x; rfl
    right_inv:=by intro x;cases x;rfl }
  have hc:Fintype.card {x:K // π.symm x.val.val.2=v}=A.card:=by
    simpa only [Fintype.card_coe] using Fintype.card_congr e
  rw [occurrence_degree_eq_filter_card]
  have hf:(Finset.univ.filter (fun x:K=>π.symm x.val.val.2=v)).card=
      Fintype.card {x:K // π.symm x.val.val.2=v}:=by
    rw [Fintype.card_subtype]
  rw [hf,hc]
  rfl
end Oberwolfach
