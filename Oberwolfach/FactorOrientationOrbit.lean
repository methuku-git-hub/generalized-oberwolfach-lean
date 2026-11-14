module

public import Oberwolfach.FactorOrientationNoTwoCycles
public import Oberwolfach.RegularCycleIsomorphism
public import Mathlib.GroupTheory.Perm.Fin

@[expose] public section
/-! The chosen successor permutation runs through every vertex in each
connected component of a two-regular factor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_cycle_orientation_reaches_component
    {X:Type*} [Fintype X] [DecidableEq X] (G:SimpleGraph X) (hG:G.IsRegularOfDegree 2)
    (e:∀C:G.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (C:G.ConnectedComponent) (a b:C):
    ∃n:ℕ,((factorCycleOrientation G e)^n) a.val=b.val:=by
  classical
  let N:=Fintype.card C
  let q:=finRotate N
  let ia:Fin N:=(e C).symm a
  let ib:Fin N:=(e C).symm b
  have h2:2≤N:=by have h3:3≤Fintype.card C:=(component_regular_two_cycle_iso G hG C).1;omega
  have hfix:∀i:Fin N,q i≠i:=by
    intro i hi
    have h:=factor_orientation_no_fixed_points G hG e (e C i).val
    apply h
    rw [factor_cycle_orientation_on_component G e C (e C i)]
    have hh:(finRotate N) ((e C).symm (e C i))=i:=by simpa [q] using hi
    simpa [N] using congrArg Subtype.val (congrArg (e C) hh)
  have hcy:q.IsCycleOn (↑(Finset.univ:Finset (Fin N)):Set (Fin N)):=by
    have hh: q.IsCycleOn {i:Fin N | q i≠i}:=(isCycle_finRotate_of_le h2).isCycleOn
    have heq:{i:Fin N | q i≠i}=Set.univ:=by ext i;simp [hfix i]
    simpa only [heq,Finset.coe_univ] using hh
  obtain ⟨m,_,hm⟩:=hcy.exists_pow_eq (Finset.mem_univ ia) (Finset.mem_univ ib)
  have hiter:∀k:ℕ,((factorCycleOrientation G e)^k) a.val=(e C ((q^k) ia)).val:=by
    intro k
    induction k with
    | zero => simp [ia]
    | succ k ih =>
      rw [pow_succ',Equiv.Perm.mul_apply,ih,factor_cycle_orientation_on_component G e C (e C ((q^k) ia))]
      simp only [RelIso.symm_apply_apply]
      simp only [pow_succ',Equiv.Perm.mul_apply,q,N]
  refine ⟨m,?_⟩
  rw [hiter m,hm]
  simp [ib]
end Oberwolfach
