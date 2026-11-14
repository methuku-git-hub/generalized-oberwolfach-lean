module

public import Oberwolfach.MarkedPartitionedResidualHost
public import Oberwolfach.LongEligibleMarkedIncomingChange

@[expose] public section
/-! An orientation of the class gives loopless, physically injective ordinary
and marked arcs after any partition of its eligible residual. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_dual_residual_physical_injective
    {V:Type} [Fintype V] [LinearOrder V] [Nonempty V]
    (S Small:SimpleGraph V) (M:V→V→ℕ)
    (hphysical:∀x y,M x y+M y x=if S.Adj x y then 1 else 0)
    (π:Equiv.Perm V) (T:Finset {a:V×V // longEligibleResidualArc M Small ⊥ a}):
    (∀e:residualOrdinaryArc (longEligibleResidualArc M Small ⊥) T,e.val.val.1≠e.val.val.2) ∧
    (∀e:residualMarkedArc (longEligibleResidualArc M Small ⊥) T,e.val.val.1≠π (π.symm e.val.val.2)) ∧
    Function.Injective (markedPhysicalEdge
      (fun e:residualOrdinaryArc (longEligibleResidualArc M Small ⊥) T=>e.val.val.1)
      (fun e:residualOrdinaryArc (longEligibleResidualArc M Small ⊥) T=>e.val.val.2)
      (fun e:residualMarkedArc (longEligibleResidualArc M Small ⊥) T=>e.val.val.1)
      (fun e:residualMarkedArc (longEligibleResidualArc M Small ⊥) T=>π.symm e.val.val.2) π):=by
  have hneq:∀x y,longEligibleResidualArc M Small ⊥ (x,y)→x≠y:=by
    intro x y he hxy
    subst y
    have hm:=he.1
    change M x x=1 at hm
    have hz:=hphysical x x
    simp only [SimpleGraph.irrefl,ite_false] at hz
    omega
  refine ⟨(fun e=>hneq _ _ e.val.property),?_,?_⟩
  · intro e
    simpa only [Equiv.apply_symm_apply] using hneq _ _ e.val.property
  · apply partitioned_residual_physical_injective (longEligibleResidualArc M Small ⊥) T π
    intro x y hxy hyx
    have hp:=hphysical x y
    have hx:=hxy.1
    have hy:=hyx.1
    change M x y=1 at hx
    change M y x=1 at hy
    split_ifs at hp <;> omega
end Oberwolfach
