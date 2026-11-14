module

public import Oberwolfach.FiniteConjunctionChanges

@[expose] public section

/-! Restriction of a centered count on an explicit outer domain. The error
increase is the number of removed coordinates, not a relative-domain error. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
variable {X:Type*} [DecidableEq X]

theorem finite_bounded_sum_restriction (A B:Finset X) (hAB:A⊆B) (f:X→ℝ)
    (hf:∀ x∈B,|f x|≤1):
    |(∑ x∈A,f x)-(∑ x∈B,f x)|≤((B\A).card:ℝ):=by
  have he: (∑ x∈B\A,f x)+(∑ x∈A,f x)=∑ x∈B,f x:=Finset.sum_sdiff hAB
  have ha:|(∑ x∈A,f x)-(∑ x∈B,f x)|=|∑ x∈B\A,f x|:=by
    rw [←he]
    ring_nf
    exact abs_neg _
  rw [ha]
  calc
    _ ≤∑ x∈B\A,|f x|:=Finset.abs_sum_le_sum_abs _ _
    _ ≤∑ x∈B\A,(1:ℝ):=Finset.sum_le_sum (fun x hx=>hf x (Finset.mem_sdiff.mp hx).1)
    _ = _:=by simp

theorem finite_centered_count_restriction (A B:Finset X) (hAB:A⊆B)
    (eligible present:X→Prop) [DecidablePred eligible] [DecidablePred present]
    (target:X→ℝ) (ht:∀ x∈B,0≤target x∧target x≤1) (ε:ℝ)
    (hcount:|(∑ x∈B.filter eligible,if present x then (1:ℝ) else 0)-
      ∑ x∈B.filter eligible,target x|<ε):
    |(∑ x∈A.filter eligible,if present x then (1:ℝ) else 0)-
      ∑ x∈A.filter eligible,target x|<ε+(B\A).card:=by
  let f:=fun x=>if eligible x then ((if present x then (1:ℝ) else 0)-target x) else 0
  have hf:∀ x∈B,|f x|≤1:=by
    intro x hx
    obtain ⟨h0,h1⟩:=ht x hx
    dsimp [f]
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  have he (C:Finset X):(∑ x∈C,f x)=
      (∑ x∈C.filter eligible,if present x then (1:ℝ) else 0)-∑ x∈C.filter eligible,target x:=by
    dsimp [f]
    rw [←Finset.sum_filter,Finset.sum_sub_distrib]
  have hd:=finite_bounded_sum_restriction A B hAB f hf
  rw [←he B] at hcount
  rw [←he A]
  have hh:|(∑ x∈A,f x)|≤|(∑ x∈A,f x)-(∑ x∈B,f x)|+|(∑ x∈B,f x)|:=by
    simpa only [sub_add_cancel] using abs_add_le ((∑ x∈A,f x)-(∑ x∈B,f x)) (∑ x∈B,f x)
  exact hh.trans_lt ((add_lt_add_of_le_of_lt hd hcount).trans_eq (add_comm _ _))

end Oberwolfach
