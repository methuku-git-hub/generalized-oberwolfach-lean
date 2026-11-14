module

public import Oberwolfach.RootedEdgeChangesOnDomain
public import Oberwolfach.MarkedConfigurationRimDeletion

@[expose] public section

/-! Degree bounds into a fixed invariant domain, including external roots.
No degree assertion is inferred from the induced graph on the domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem physical_deletion_invariant_domain_sum
    (D:SimpleGraph V) (π:Equiv.Perm V) (A:Finset V) (hA:∀ x,π x∈A↔x∈A)
    (delta:ℝ) (hD:∀ x,((D.neighborFinset x∩A).card:ℝ)≤delta):
    ∀ b x,(∑ y:A,if D.Adj x (optionalSuccessor π b y.val) then (1:ℝ) else 0)≤delta:=by
  have h0 (x:V):(∑ y:A,if D.Adj x y.val then (1:ℝ) else 0)≤delta:=by
    have he:(∑ y:A,if D.Adj x y.val then (1:ℝ) else 0)=((D.neighborFinset x∩A).card:ℝ):=by
      rw [Finset.sum_coe_sort A (fun y:V=>if D.Adj x y then (1:ℝ) else 0)]
      simp only [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]
      congr 1
      congr 1
      ext y
      simp only [Finset.mem_filter,Finset.mem_inter,SimpleGraph.mem_neighborFinset]
      tauto
    exact he.trans_le (hD x)
  intro b x
  cases b
  · simpa only [optionalSuccessor,Bool.false_eq_true,ite_false] using h0 x
  · let f:A→A:=fun y=>⟨π y.val,(hA y.val).mpr y.property⟩
    have hf:Function.Injective f:=by intro y z he;apply Subtype.ext;exact π.injective (congrArg Subtype.val he)
    have hh:=finite_injective_sum_le f hf (fun y:A=>if D.Adj x y.val then (1:ℝ) else 0)
      (fun _=>by positivity)
    exact hh.trans (h0 x)

end Oberwolfach
