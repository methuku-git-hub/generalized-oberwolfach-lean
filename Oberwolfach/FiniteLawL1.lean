module

public import Oberwolfach.FiniteOptionProduct
public import Oberwolfach.FiniteLawMap
public import Mathlib.Data.Fintype.Option

@[expose] public section

/-! The elementary L1 distance of two finite probability mass functions,
and its behaviour under products and deterministic maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def FiniteLaw.l1Distance {Ω : Type*} [Fintype Ω] (μ ν : FiniteLaw Ω) : ℝ :=
  ∑ x,|μ.mass x-ν.mass x|

theorem finiteLaw_l1_nonneg {Ω : Type*} [Fintype Ω] (μ ν : FiniteLaw Ω) :
    0≤μ.l1Distance ν := Finset.sum_nonneg (fun _ _=>abs_nonneg _)

theorem finiteLaw_probability_l1 {Ω : Type*} [Fintype Ω]
    (μ ν : FiniteLaw Ω) (A : Ω → Prop) :
    |μ.probability A-ν.probability A|≤μ.l1Distance ν := by
  classical
  unfold FiniteLaw.probability FiniteLaw.l1Distance
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : A x <;> simp only [hx,ite_true,ite_false,sub_self,abs_zero]
  · exact le_refl _
  · exact abs_nonneg _

theorem finiteLaw_l1_map {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ ν : FiniteLaw Ω) (f : Ω → Γ) :
    (μ.map f).l1Distance (ν.map f)≤μ.l1Distance ν := by
  classical
  unfold FiniteLaw.l1Distance
  calc
    _ ≤ ∑ y,∑ x,if f x=y then |μ.mass x-ν.mass x| else 0 := by
      apply Finset.sum_le_sum
      intro y _
      simp only [FiniteLaw.map]
      rw [← Finset.sum_sub_distrib]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro x _
      by_cases he : f x=y <;> simp [he]
    _ = _ := by rw [Finset.sum_comm];simp

theorem finiteLaw_l1_prod {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ ν : FiniteLaw Ω) (ρ σ : FiniteLaw Γ) :
    (μ.prod ρ).l1Distance (ν.prod σ)≤μ.l1Distance ν+ρ.l1Distance σ := by
  classical
  have hpoint (x : Ω) (y : Γ) : |μ.mass x*ρ.mass y-ν.mass x*σ.mass y|≤
      |μ.mass x-ν.mass x| *ρ.mass y+ν.mass x*|ρ.mass y-σ.mass y| := by
    calc
      _ = |(μ.mass x-ν.mass x)*ρ.mass y+ν.mass x*(ρ.mass y-σ.mass y)| := by congr 1;ring
      _ ≤ |(μ.mass x-ν.mass x)*ρ.mass y|+|ν.mass x*(ρ.mass y-σ.mass y)| := abs_add_le _ _
      _ = _ := by rw [abs_mul,abs_mul,abs_of_nonneg (ρ.nonneg y),abs_of_nonneg (ν.nonneg x)]
  unfold FiniteLaw.l1Distance
  rw [Fintype.sum_prod_type]
  change (∑ x,∑ y,|μ.mass x*ρ.mass y-ν.mass x*σ.mass y|)≤_
  calc
    _ ≤ ∑ x,∑ y,(|μ.mass x-ν.mass x| *ρ.mass y+ν.mass x*|ρ.mass y-σ.mass y|) :=
      Finset.sum_le_sum (fun x _=>Finset.sum_le_sum (fun y _=>hpoint x y))
    _ = _ := by
      simp_rw [Finset.sum_add_distrib,← Finset.mul_sum,ρ.total,mul_one]
      rw [← Finset.sum_mul,ν.total,one_mul]

theorem finiteLaw_l1_pi_reindex
    {I J Ω : Type*} [Fintype I] [Fintype J] [Fintype Ω]
    (e : I ≃ J) (μ ν : J → FiniteLaw Ω) :
    (FiniteLaw.pi μ).l1Distance (FiniteLaw.pi ν)=
      (FiniteLaw.pi (fun i=>μ (e i))).l1Distance (FiniteLaw.pi (fun i=>ν (e i))) := by
  classical
  unfold FiniteLaw.l1Distance
  rw [← (Equiv.piCongrLeft (fun _ : J=>Ω) e).sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  change |(∏ j,(μ j).mass ((Equiv.piCongrLeft (fun _ : J=>Ω) e x) j))-
    (∏ j,(ν j).mass ((Equiv.piCongrLeft (fun _ : J=>Ω) e x) j))|=
      |(∏ i,(μ (e i)).mass (x i))-(∏ i,(ν (e i)).mass (x i))|
  rw [← e.prod_comp (fun j=>(μ j).mass ((Equiv.piCongrLeft (fun _ : J=>Ω) e x) j)),
    ← e.prod_comp (fun j=>(ν j).mass ((Equiv.piCongrLeft (fun _ : J=>Ω) e x) j))]
  simp only [Equiv.piCongrLeft_apply_apply]

theorem finiteLaw_l1_pi_option
    {I Ω : Type*} [Fintype I] [Fintype Ω]
    (μ ν : Option I → FiniteLaw Ω) :
    (FiniteLaw.pi μ).l1Distance (FiniteLaw.pi ν)=
      ((μ none).prod (FiniteLaw.pi (fun i=>μ (some i)))).l1Distance
        ((ν none).prod (FiniteLaw.pi (fun i=>ν (some i)))) := by
  classical
  unfold FiniteLaw.l1Distance
  rw [← (Equiv.piOptionEquivProd (β:=fun _ : Option I=>Ω)).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  simp only [FiniteLaw.pi,FiniteLaw.prod,Fintype.prod_option,
    Equiv.piOptionEquivProd,Equiv.coe_fn_symm_mk]

theorem finiteLaw_l1_pi
    {I Ω : Type*} [Fintype I] [Fintype Ω] (μ ν : I → FiniteLaw Ω) :
    (FiniteLaw.pi μ).l1Distance (FiniteLaw.pi ν)≤∑ i,(μ i).l1Distance (ν i) := by
  classical
  revert μ ν
  refine Fintype.induction_empty_option
    (P:=fun J _=>∀ μ ν : J → FiniteLaw Ω,
      (FiniteLaw.pi μ).l1Distance (FiniteLaw.pi ν)≤∑ j,(μ j).l1Distance (ν j)) ?_ ?_ ?_ I
  · intro J K _ e ih μ ν
    letI : Fintype J := Fintype.ofEquiv K e.symm
    rw [finiteLaw_l1_pi_reindex e μ ν]
    exact (ih (fun i=>μ (e i)) (fun i=>ν (e i))).trans_eq
      (e.sum_comp (fun j=>(μ j).l1Distance (ν j)))
  · intro μ ν
    simp [FiniteLaw.l1Distance,FiniteLaw.pi]
  · intro J _ ih μ ν
    have he : (fun a b : Option J=>Classical.propDecidable (a=b))=
        (@Option.instDecidableEq J (Classical.decEq J)) := Subsingleton.elim _ _
    rw [he]
    rw [finiteLaw_l1_pi_option]
    have hh := finiteLaw_l1_prod (μ none) (ν none)
      (FiniteLaw.pi (fun i=>μ (some i))) (FiniteLaw.pi (fun i=>ν (some i)))
    have hi := ih (fun i=>μ (some i)) (fun i=>ν (some i))
    rw [Fintype.sum_option]
    exact hh.trans (add_le_add (le_refl _) hi)

end Oberwolfach
