module

public import Oberwolfach.LongPreparationFamilySeeds
public import Oberwolfach.LongPreparationFamilyRetainedLengths

@[expose] public section
/-! Restrict the hub coefficient sums to the global family of retained lengths. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_preparation_retained_coefficient_sum {U:Type} [Fintype U] {n:ℕ}
    (F:U→SimpleGraph (Fin n)) (hF:∀ u,(F u).IsRegularOfDegree 2)
    (K:ℕ) (θ:ℝ) (b:U→ℝ):
    let fraction:=fun (u:U) (i:Fin K)=>
      ((Finset.univ.filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=some i)).card:ℝ)/n
    let retained:=Finset.univ.filter (fun i=>∃ u,θ/(100*(K:ℝ))≤fraction u i)
    let η:=fun i u=>(1-θ)*(if θ/(100*(K:ℝ))≤fraction u i then fraction u i else 0)/b u;
    ∀ u,(∑ i:{i:Fin K // i∈retained},η i.val u)=∑ i,η i u:=by
  intro fraction retained η u
  change (∑ i:↥retained,(fun x=>η x u) i.val)=∑ i,η i u
  rw [Finset.sum_coe_sort retained (fun x=>η x u)]
  apply Finset.sum_subset (Finset.subset_univ retained)
  intro i _ hi
  have hn:¬θ/(100*(K:ℝ))≤fraction u i:=by
    intro h
    apply hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,u,h⟩
  simp [η,hn]
end Oberwolfach
