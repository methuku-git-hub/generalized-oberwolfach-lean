module

public import Oberwolfach.MarkedPermutationIntervalGeometry

@[expose] public section
/-! A successor of an interval root is either another root of the same
interval or its final endpoint. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_interval_successor_root_or_endpoint
    {V I:Type} [Fintype V] [Fintype I] [DecidableEq V]
    (π:Equiv.Perm V) (d:ℕ) (a:I→V) (v:V)
    (hv:v∈markedIntervalRootSet π (fun _=>d) a):
    π v∈markedIntervalRootSet π (fun _=>d) a ∨ ∃i:I,π v=(π^d) (a i):=by
  obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hv
  obtain ⟨j,_,hj⟩:=Finset.mem_image.mp hi
  by_cases h:j.val+1<d
  · left
    apply Finset.mem_biUnion.mpr
    refine ⟨i,Finset.mem_univ _,?_⟩
    apply Finset.mem_image.mpr
    refine ⟨⟨j.val+1,h⟩,Finset.mem_univ _,?_⟩
    simp only [pow_succ',Equiv.Perm.mul_apply]
    rw [hj]
  · right
    refine ⟨i,?_⟩
    have hlast:j.val+1=d:=by have hjlt : j.val<d := j.isLt; omega
    rw [←hlast,pow_succ',Equiv.Perm.mul_apply,hj]
end Oberwolfach
