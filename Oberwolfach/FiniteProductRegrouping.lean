module

public import Oberwolfach.FiniteLawMap

@[expose] public section

/-! Exact identities for regrouping independent coordinates. These preserve
joint probabilities, rather than replacing an experiment by matching marginals. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_prod_map_left_probability
    {Ω Γ Ξ : Type*} [Fintype Ω] [Fintype Γ] [Fintype Ξ]
    (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) (f : Ω→Ξ) (E : Ξ→Γ→Prop) :
    (μ.prod ν).probability (fun z=>E (f z.1) z.2)=
      ((μ.map f).prod ν).probability (fun z=>E z.1 z.2) := by
  have hleft : (μ.prod ν).probability (fun z=>E (f z.1) z.2)=
      ∑ γ,ν.mass γ*μ.probability (fun ω=>E (f ω) γ) := by
    unfold FiniteLaw.probability
    rw [Fintype.sum_prod_type,Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro γ _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    simp only [FiniteLaw.prod]
    split_ifs <;> ring
  have hright : ((μ.map f).prod ν).probability (fun z=>E z.1 z.2)=
      ∑ γ,ν.mass γ*(μ.map f).probability (fun ξ=>E ξ γ) := by
    unfold FiniteLaw.probability
    rw [Fintype.sum_prod_type,Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro γ _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ξ _
    simp only [FiniteLaw.prod]
    split_ifs <;> ring
  rw [hleft,hright]
  simp_rw [finiteLaw_map_probability]

theorem finiteLaw_prod_first_probability
    {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) (E : Ω→Prop) :
    (μ.prod ν).probability (fun z=>E z.1)=μ.probability E := by
  unfold FiniteLaw.probability
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : E ω
  · simp only [h,ite_true,FiniteLaw.prod,← Finset.mul_sum,ν.total,mul_one]
  · simp only [h,ite_false,Finset.sum_const_zero]

theorem finiteLaw_pi_prod_probability
    {I : Type*} [Fintype I] [DecidableEq I]
    {A B : I→Type*} [∀ i,Fintype (A i)] [∀ i,Fintype (B i)]
    (μ : ∀ i,FiniteLaw (A i)) (ν : ∀ i,FiniteLaw (B i))
    (E : (∀ i,A i)→(∀ i,B i)→Prop) :
    ((FiniteLaw.pi μ).prod (FiniteLaw.pi ν)).probability (fun z=>E z.1 z.2)=
      (FiniteLaw.pi (fun i=>(μ i).prod (ν i))).probability
        (fun σ=>E (fun i=>(σ i).1) (fun i=>(σ i).2)) := by
  let e : ((∀ i,A i)×(∀ i,B i))≃(∀ i,A i×B i) :=
    { toFun := fun z i=>(z.1 i,z.2 i)
      invFun := fun σ=>(fun i=>(σ i).1,fun i=>(σ i).2)
      left_inv := by intro z;cases z;rfl
      right_inv := by intro σ;rfl }
  unfold FiniteLaw.probability
  rw [← e.symm.sum_comp]
  apply Finset.sum_congr rfl
  intro σ _
  change (if E (fun i=>(σ i).1) (fun i=>(σ i).2) then
    (∏ i,(μ i).mass (σ i).1)*(∏ i,(ν i).mass (σ i).2) else 0)=
    if E (fun i=>(σ i).1) (fun i=>(σ i).2) then
      ∏ i,(μ i).mass (σ i).1*(ν i).mass (σ i).2 else 0
  rw [Finset.prod_mul_distrib]

end Oberwolfach
