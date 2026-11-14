module

public import Oberwolfach.MarkedHostRimEncoding
public import Mathlib.Data.Finset.Basic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [LinearOrder V]
local instance partitionResidualDecEq : DecidableEq V := Classical.decEq V
local instance partitionResidualArcDecEq (P:V×V→Prop):DecidableEq {e:V×V // P e}:=Classical.decEq _

def residualOrdinaryArc (P:V×V→Prop) (M:Finset {e:V×V // P e}):Type := {e:{a:V×V // P a} // e∉M}
def residualMarkedArc (P:V×V→Prop) (M:Finset {e:V×V // P e}):Type := {e:{a:V×V // P a} // e∈M}

theorem partitioned_residual_physical_injective
    (P:V×V→Prop) (M:Finset {e:V×V // P e}) (π:Equiv.Perm V)
    (hAnti:∀x y,P (x,y)→P (y,x)→False):
    Function.Injective (markedPhysicalEdge
      (fun e:residualOrdinaryArc P M=>e.val.val.1) (fun e=>e.val.val.2)
      (fun e:residualMarkedArc P M=>e.val.val.1) (fun e=>π.symm e.val.val.2) π):=by
  have hpairs (a b:{e:V×V // P e})
      (h:({a.val.1,a.val.2}:Finset V)={b.val.1,b.val.2}):a=b:=by
    have he: a.val.1=b.val.1 ∧ a.val.2=b.val.2 ∨ a.val.1=b.val.2 ∧ a.val.2=b.val.1:=by
      apply Set.pair_eq_pair_iff.mp
      simpa only [Finset.coe_pair] using congrArg (fun S:Finset V=>(S:Set V)) h
    rcases he with h|h
    · exact Subtype.ext (Prod.ext h.1 h.2)
    · have hrev:P (a.val.2,a.val.1):=by simpa only [h.1,h.2] using b.property
      exact False.elim (hAnti a.val.1 a.val.2 a.property hrev)
  intro a b h
  cases a with
  | inl a=>
    cases b with
    | inl b=>
      have hh:a.val=b.val:=hpairs a.val b.val (by simpa [markedPhysicalEdge] using h)
      exact congrArg Sum.inl (Subtype.ext hh)
    | inr b=>
      have hh:a.val=b.val:=hpairs a.val b.val (by simpa [markedPhysicalEdge] using h)
      exact False.elim (a.property (hh ▸ b.property))
  | inr a=>
    cases b with
    | inl b=>
      have hh:a.val=b.val:=hpairs a.val b.val (by simpa [markedPhysicalEdge] using h)
      exact False.elim (b.property (hh ▸ a.property))
    | inr b=>
      have hh:a.val=b.val:=hpairs a.val b.val (by simpa [markedPhysicalEdge] using h)
      exact congrArg Sum.inr (Subtype.ext hh)
end Oberwolfach
