module

public import Oberwolfach.FiberwiseCandidateAssignment
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section
/-! Counting vertices in classes of a common prescribed size. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem card_of_uniform_fibers {V C:Type} [Fintype V] [DecidableEq V] [DecidableEq C]
    (f:V→C) (T:Finset C) (r:ℕ)
    (hsize:∀c∈T,(Finset.univ.filter (fun v=>f v=c)).card=r):
    (Finset.univ.filter (fun v=>f v∈T)).card=r*T.card :=by
  let fiber:=fun c=>Finset.univ.filter (fun v=>f v=c)
  have hunion:T.biUnion fiber=Finset.univ.filter (fun v=>f v∈T):=by
    ext v
    simp only [Finset.mem_biUnion,fiber,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨c,hc,rfl⟩;exact hc
    · intro hv;exact ⟨f v,hv,rfl⟩
  have hdis:∀c∈T,∀d∈T,c≠d→Disjoint (fiber c) (fiber d):=by
    intro c hc d hd hcd
    apply Finset.disjoint_left.mpr
    intro v hv hw
    have hvc:f v=c:=(Finset.mem_filter.mp hv).2
    have hvd:f v=d:=(Finset.mem_filter.mp hw).2
    exact hcd (hvc.symm.trans hvd)
  rw [←hunion,Finset.card_biUnion hdis]
  calc
    _ = ∑c∈T,r := by
      apply Finset.sum_congr rfl
      intro c hc
      exact hsize c hc
    _ = _ := by simp [Nat.mul_comm]
end Oberwolfach
