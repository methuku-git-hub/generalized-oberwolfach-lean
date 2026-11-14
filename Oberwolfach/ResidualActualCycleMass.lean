module

public import Oberwolfach.ResidualActualData
public import Oberwolfach.TwoRegularComponents

@[expose] public section
/-! The embedded cycle vertices have exactly the total assigned cycle mass. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_residual_cycle_mass
    {V K J:Type} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq K] [DecidableEq J]
    {F:SimpleGraph V} (a:ActualResidualData (K:=K) (J:=J) F)
    (ht:a.t=Finset.univ)
    (hC:a.Cembed=a.t.biUnion (fun j=>(a.C j).support.toFinset)):
    a.Cembed.card=∑j:J,(a.C j).length:=by
  rw [hC,ht,Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro j hj
    have hc: (a.C j).IsCycle:=a.hcycle j (by rw [ht];exact Finset.mem_univ _)
    have hh:=cycle_length_eq_support_ncard hc
    have heq:({x | x∈(a.C j).support}:Set V)=↑((a.C j).support.toFinset):=by
      ext x; simp
    rw [heq,Set.ncard_coe_finset] at hh
    exact hh.symm
  · intro i hi j hj hne
    exact a.hC (by rw [ht];exact Finset.mem_univ _) (by rw [ht];exact Finset.mem_univ _) hne
end Oberwolfach
