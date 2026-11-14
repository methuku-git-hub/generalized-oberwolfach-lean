module

public import Oberwolfach.CommonEvents

@[expose] public section

/-! Union bounds over vertices of a sampled set. The number of tests is the
sample size, with the root event kept inside every probability. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem selected_set_probability_sum {V Ω : Type*} [Fintype V] [Fintype Ω]
    (μ : FiniteLaw Ω) (S : Ω → Finset V) (m : ℕ) (hm : ∀ ω,(S ω).card=m)
    (E : Ω → Prop) :
    (∑ x,μ.probability (fun ω => E ω ∧ x∈S ω))=(m:ℝ)*μ.probability E := by
  unfold FiniteLaw.probability
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hE : E ω
  · simp only [hE,true_and,ite_true]
    have he : (∑ x,if x∈S ω then μ.mass ω else 0)=(S ω).card*μ.mass ω := by
      simp
    rw [he,hm]
  · simp [hE]

theorem selected_set_union_bound {V Ω : Type*} [Fintype V] [Fintype Ω]
    (μ : FiniteLaw Ω) (S : Ω → Finset V) (m : ℕ) (hm : ∀ ω,(S ω).card=m)
    (E : Ω → Prop) (Bad : V → Ω → Prop) (ε : ℝ)
    (hbad : ∀ x,μ.probability (fun ω => E ω ∧ x∈S ω ∧ Bad x ω)≤
      ε*μ.probability (fun ω => E ω ∧ x∈S ω)) :
    μ.probability (fun ω => E ω ∧ ∃ x∈S ω,Bad x ω)≤
      ε*m*μ.probability E := by
  have hu : μ.probability (fun ω => E ω ∧ ∃ x∈S ω,Bad x ω)≤
      ∑ x,μ.probability (fun ω => E ω ∧ x∈S ω ∧ Bad x ω) := by
    unfold FiniteLaw.probability
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro ω _
    by_cases hb : E ω ∧ ∃ x∈S ω,Bad x ω
    · obtain ⟨hE,x,hx,hB⟩ := hb
      rw [if_pos ⟨hE,x,hx,hB⟩]
      have hh := Finset.single_le_sum (s:=Finset.univ)
        (f:=fun x => if E ω ∧ x∈S ω ∧ Bad x ω then μ.mass ω else 0)
        (fun x _ => by split_ifs;exact μ.nonneg ω;exact le_refl _) (Finset.mem_univ x)
      have hhE : E ω ∧ x∈S ω ∧ Bad x ω := ⟨hE,hx,hB⟩
      rw [if_pos hhE] at hh
      convert hh using 1
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> rfl
    · rw [if_neg hb]
      exact Finset.sum_nonneg (fun x _ => by split_ifs;exact μ.nonneg ω;exact le_refl _)
  calc
    _ ≤ ∑ x,μ.probability (fun ω => E ω ∧ x∈S ω ∧ Bad x ω) := hu
    _ ≤ ∑ x,ε*μ.probability (fun ω => E ω ∧ x∈S ω) :=
      Finset.sum_le_sum (fun x _ => hbad x)
    _ = _ := by rw [← Finset.mul_sum,selected_set_probability_sum μ S m hm E];ring

end Oberwolfach
