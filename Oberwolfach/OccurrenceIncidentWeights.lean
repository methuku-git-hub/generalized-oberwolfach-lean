module

public import Oberwolfach.RelationIncidentWeights

@[expose] public section

/-! Deterministic costs of deleted edge occurrences, allowing multiple
types and retaining their endpoint fibers. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_fiber_membership_sum {E V : Type*} [Fintype E] [DecidableEq V]
    (f : E → V) (a : E → ℝ) (S : Finset V) :
    (∑ e,if f e∈S then a e else 0)=∑ x∈S,∑ e,if f e=x then a e else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : f e∈S <;> simp [he,Finset.sum_ite_eq']

theorem occurrence_root_incident_cost {E V : Type*} [Fintype E] [Fintype V] [DecidableEq V]
    (f g : E → V) (D : E → Prop) (d : ℝ)
    (hout : ∀ x,(∑ e,if D e ∧ f e=x then (1:ℝ) else 0)≤d)
    (hin : ∀ y,(∑ e,if D e ∧ g e=y then (1:ℝ) else 0)≤d)
    (S T : Finset V) (M N : ℝ) (hM : 0≤M) (hN : 0≤N) :
    (∑ e,if D e then (if f e∈S ∨ g e∈T then M else N) else 0)≤
      d*((S.card+T.card:ℝ)*M+(Fintype.card V:ℝ)*N) := by
  let a (e : E) : ℝ := if D e then 1 else 0
  have hf (x : V) : (∑ e,if f e=x then a e else 0)≤d := by
    convert hout x using 1
    apply Finset.sum_congr rfl
    intro e _
    dsimp only [a]
    split_ifs <;> simp_all
  have hg (x : V) : (∑ e,if g e=x then a e else 0)≤d := by
    convert hin x using 1
    apply Finset.sum_congr rfl
    intro e _
    dsimp only [a]
    split_ifs <;> simp_all
  have hS : (∑ e,if f e∈S then a e else 0)≤S.card*d := by
    rw [finite_fiber_membership_sum]
    calc
      _ ≤ ∑ _x∈S,d := Finset.sum_le_sum (fun x _=>hf x)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
  have hT : (∑ e,if g e∈T then a e else 0)≤T.card*d := by
    rw [finite_fiber_membership_sum]
    calc
      _ ≤ ∑ _x∈T,d := Finset.sum_le_sum (fun x _=>hg x)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
  have htotal : (∑ e,a e)≤Fintype.card V*d := by
    have hh := finite_fiber_membership_sum f a Finset.univ
    simp only [Finset.mem_univ,ite_true] at hh
    rw [hh]
    calc
      _ ≤ ∑ _x : V,d := Finset.sum_le_sum (fun x _=>hf x)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  calc
    _ ≤ ∑ e,((if f e∈S then a e else 0)*M+(if g e∈T then a e else 0)*M+a e*N) := by
      apply Finset.sum_le_sum
      intro e _
      dsimp only [a]
      split_ifs <;> simp_all <;> linarith
    _ = (∑ e,if f e∈S then a e else 0)*M+(∑ e,if g e∈T then a e else 0)*M+(∑ e,a e)*N := by
      simp only [Finset.sum_add_distrib,Finset.sum_mul]
    _ ≤ _ := by
      have h1 := mul_le_mul_of_nonneg_right hS hM
      have h2 := mul_le_mul_of_nonneg_right hT hM
      have h3 := mul_le_mul_of_nonneg_right htotal hN
      nlinarith only [h1,h2,h3]

end Oberwolfach
