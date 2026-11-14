module

public import Oberwolfach.CommonEvents

@[expose] public section

/-! The finite asymmetric Lovász local lemma. Independence is stated as an
exact equality for a bad event and the avoidance of any set of non-neighbours. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Ω I : Type*} [Fintype Ω] [DecidableEq I]

def avoidsEvents (A : I → Ω → Prop) (S : Finset I) (ω : Ω) : Prop :=
  ∀ i∈S,¬A i ω

theorem finiteLaw_avoidance_split (μ : FiniteLaw Ω) (A : I → Ω → Prop)
    (S : Finset I) (i : I) :
    μ.probability (avoidsEvents A (insert i S))+
      μ.probability (fun ω=>A i ω ∧ avoidsEvents A S ω)=μ.probability (avoidsEvents A S) := by
  unfold FiniteLaw.probability
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  have hh : avoidsEvents A (insert i S) ω ↔ ¬A i ω ∧ avoidsEvents A S ω := by
    simp only [avoidsEvents,Finset.mem_insert,forall_eq_or_imp]
  simp only [hh]
  by_cases hA : A i ω <;> by_cases hS : avoidsEvents A S ω <;> simp [hA,hS]

theorem finiteLaw_avoidance_product (μ : FiniteLaw Ω) (A : I → Ω → Prop)
    (x : I → ℝ) (hx : ∀ i,0≤1-x i) (T U : Finset I)
    (hc : ∀ K⊆U,∀ i∈U,i∉K →
      μ.probability (fun ω=>A i ω ∧ avoidsEvents A (T∪K) ω)≤
        x i*μ.probability (avoidsEvents A (T∪K))) :
    μ.probability (avoidsEvents A T)*(∏ i∈U,(1-x i))≤
      μ.probability (avoidsEvents A (T∪U)) := by
  induction U using Finset.induction_on with
  | empty => simp
  | @insert i U hi ih =>
    have hcU : ∀ K⊆U,∀ j∈U,j∉K →
        μ.probability (fun ω=>A j ω ∧ avoidsEvents A (T∪K) ω)≤
          x j*μ.probability (avoidsEvents A (T∪K)) :=
      fun K hK j hj hjK=>hc K (hK.trans (Finset.subset_insert _ _)) j (Finset.mem_insert_of_mem hj) hjK
    have hprev := ih hcU
    have hstep := hc U (Finset.subset_insert _ _) i (Finset.mem_insert_self _ _) hi
    have hsplit := finiteLaw_avoidance_split μ A (T∪U) i
    have he : T∪insert i U=insert i (T∪U) := by ext;simp [or_left_comm]
    rw [he,Finset.prod_insert hi]
    calc
      _ = (1-x i)*(μ.probability (avoidsEvents A T)*∏ j∈U,(1-x j)) := by ring
      _ ≤ (1-x i)*μ.probability (avoidsEvents A (T∪U)) :=
        mul_le_mul_of_nonneg_left hprev (hx i)
      _ ≤ _ := by linarith

theorem finiteLaw_localLemma_conditional (μ : FiniteLaw Ω) (A : I → Ω → Prop)
    (N : I → Finset I) (x : I → ℝ)
    (hx0 : ∀ i,0≤x i) (hx1 : ∀ i,x i<1)
    (hind : ∀ i T,i∉T → Disjoint T (N i) →
      μ.probability (fun ω=>A i ω ∧ avoidsEvents A T ω)=
        μ.probability (A i)*μ.probability (avoidsEvents A T))
    (hsmall : ∀ i,μ.probability (A i)≤x i*∏ j∈N i,(1-x j))
    (S : Finset I) (i : I) (hi : i∉S) :
    μ.probability (fun ω=>A i ω ∧ avoidsEvents A S ω)≤
      x i*μ.probability (avoidsEvents A S) := by
  revert i
  refine Finset.strongInductionOn S ?_
  intro S ih i hi
  let T := S\N i
  let U := S∩N i
  have hT : T⊆S := Finset.sdiff_subset
  have hU : U⊆S := Finset.inter_subset_left
  have hTU : T∪U=S := by ext j;simp [T,U];tauto
  have hden : μ.probability (avoidsEvents A T)*(∏ j∈U,(1-x j))≤
      μ.probability (avoidsEvents A S) := by
    rw [← hTU]
    apply finiteLaw_avoidance_product μ A x (fun j=>(sub_pos.mpr (hx1 j)).le)
    intro K hK j hj hjK
    have hjN : j∈N i := (Finset.mem_inter.mp hj).2
    have hjT : j∉T := by simp only [T,Finset.mem_sdiff,not_and];exact fun _=>not_not_intro hjN
    have hjTK : j∉T∪K := by simp only [Finset.mem_union,not_or];exact ⟨hjT,hjK⟩
    have hsub : T∪K⊆S := Finset.union_subset hT (hK.trans hU)
    have hproper : T∪K⊂S := Finset.ssubset_iff_subset_ne.mpr ⟨hsub,by
      intro heq
      exact hjTK (heq.symm ▸ hU hj)⟩
    exact ih (T∪K) hproper j hjTK
  have hnum : μ.probability (fun ω=>A i ω ∧ avoidsEvents A S ω)≤
      μ.probability (A i)*μ.probability (avoidsEvents A T) := by
    rw [← hind i T (fun h=>hi (hT h)) (Finset.disjoint_left.mpr (fun j hj hjN=>(Finset.mem_sdiff.mp hj).2 hjN))]
    apply finiteLaw_probability_mono
    intro ω h
    exact ⟨h.1,fun j hj=>h.2 j (hT hj)⟩
  have hprod : (∏ j∈N i,(1-x j))≤∏ j∈U,(1-x j) := by
    apply Finset.prod_le_prod_of_subset_of_le_one₀ (Finset.inter_subset_right)
    · intro j _;exact (sub_pos.mpr (hx1 j)).le
    · intro j _ _;linarith [hx0 j]
  calc
    _ ≤ μ.probability (A i)*μ.probability (avoidsEvents A T) := hnum
    _ ≤ (x i*(∏ j∈N i,(1-x j)))*μ.probability (avoidsEvents A T) :=
      mul_le_mul_of_nonneg_right (hsmall i) (finiteLaw_probability_nonneg _ _)
    _ ≤ (x i*(∏ j∈U,(1-x j)))*μ.probability (avoidsEvents A T) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (hx0 i))
        (finiteLaw_probability_nonneg _ _)
    _ = x i*(μ.probability (avoidsEvents A T)*(∏ j∈U,(1-x j))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (hx0 i)

theorem finiteLaw_localLemma (μ : FiniteLaw Ω) (A : I → Ω → Prop)
    (N : I → Finset I) (x : I → ℝ)
    (hx0 : ∀ i,0≤x i) (hx1 : ∀ i,x i<1)
    (hind : ∀ i T,i∉T → Disjoint T (N i) →
      μ.probability (fun ω=>A i ω ∧ avoidsEvents A T ω)=
        μ.probability (A i)*μ.probability (avoidsEvents A T))
    (hsmall : ∀ i,μ.probability (A i)≤x i*∏ j∈N i,(1-x j))
    (S : Finset I) :
    0<μ.probability (avoidsEvents A S) := by
  have h := finiteLaw_avoidance_product μ A x (fun j=>(sub_pos.mpr (hx1 j)).le) ∅ S
    (by
      intro K _ i _ hi
      simpa only [Finset.empty_union] using
        finiteLaw_localLemma_conditional μ A N x hx0 hx1 hind hsmall K i hi)
  have hempty : μ.probability (avoidsEvents A ∅)=1 := by
    unfold FiniteLaw.probability
    simp only [avoidsEvents,Finset.notMem_empty,IsEmpty.forall_iff,implies_true,ite_true]
    exact μ.total
  rw [hempty,one_mul,Finset.empty_union] at h
  exact (Finset.prod_pos (fun i _=>sub_pos.mpr (hx1 i))).trans_le h

end Oberwolfach
