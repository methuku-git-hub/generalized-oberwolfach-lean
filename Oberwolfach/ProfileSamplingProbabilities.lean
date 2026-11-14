module

public import Oberwolfach.ProfileRootSampling
public import Oberwolfach.SubsetInclusion
public import Oberwolfach.FiniteCoordinateEvents

@[expose] public section

/-! Exact classwise fixed-size inclusion probabilities. The equalities
use the original independent uniform subset law in each class; no
independence between overlapping cycle events is required. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]

theorem profile_subset_inclusion_probability (m : I → ℕ)
    [∀ i,Nonempty (FixedSubset (V i) (m i))]
    (hm : ∀ i,m i ≤ Fintype.card (V i)) (A : Finset (Σ i,V i)) :
    (FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (m i)))).probability
      (fun σ => A⊆profileRootSet σ)=
      ∏ i,((m i).choose (Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈A)).card:ℝ)/
        (Fintype.card (V i)).choose (Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈A)).card := by
  let A' (i : I) := Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈A)
  have hp (σ : ∀ i,FixedSubset (V i) (m i)) : A⊆profileRootSet σ ↔ ∀ i,A' i⊆(σ i).val := by
    constructor
    · intro h i v hv
      exact (profileRootSet_mem σ i v).mp (h (Finset.mem_filter.mp hv).2)
    · intro h v hv
      rcases v with ⟨i,v⟩
      exact (profileRootSet_mem σ i v).mpr (h i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩))
  have he : (fun σ : ∀ i,FixedSubset (V i) (m i) => A⊆profileRootSet σ)=
      (fun σ => ∀ i,A' i⊆(σ i).val) := funext (fun σ => propext (hp σ))
  rw [he]
  calc
    _ = ∏ i,(FiniteLaw.uniform (FixedSubset (V i) (m i))).probability (fun S => A' i⊆S.val) := by
      convert finiteLaw_pi_probability_forall
        (fun i => FiniteLaw.uniform (FixedSubset (V i) (m i)))
        (fun i (S : FixedSubset (V i) (m i)) => A' i⊆S.val) using 1 <;> congr!
    _ = _ := Finset.prod_congr rfl (fun i _ => fixedSubset_joint_inclusion (hm i) (A' i))

theorem profile_resource_weight_expectation {C : Type*} [Fintype C]
    (m a : I → ℕ) [∀ i,Nonempty (FixedSubset (V i) (m i))]
    (hm : ∀ i,m i ≤ Fintype.card (V i)) (R : C → Finset (Σ i,V i)) (w : C → ℝ)
    (hR : ∀ C₀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈R C₀)).card=a i) :
    (FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (m i)))).expectation
      (fun σ => ∑ C₀,if R C₀⊆profileRootSet σ then w C₀ else 0)=
      (∏ i,((m i).choose (a i):ℝ)/(Fintype.card (V i)).choose (a i))*(∑ C₀,w C₀) := by
  rw [finiteLaw_expectation_sum]
  have he (C₀ : C) :
      (FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (m i)))).expectation
        (fun σ => if R C₀⊆profileRootSet σ then w C₀ else 0)=
      w C₀*(∏ i,((m i).choose (a i):ℝ)/(Fintype.card (V i)).choose (a i)) := by
    rw [finiteLaw_expectation_indicator_value,profile_subset_inclusion_probability m hm]
    simp only [hR]
  simp_rw [he]
  rw [← Finset.sum_mul,mul_comm]

end Oberwolfach
