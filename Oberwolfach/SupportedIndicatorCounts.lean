module

public import Oberwolfach.SupportedPatternSums

@[expose] public section

/-! Counts on fixed domains from locally determined Boolean indicators.
The domain is fixed before sampling; overlapping primitive supports are
controlled by their read and influence multiplicities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A E : Type*} [Fintype A] [Fintype E] [DecidableEq A] [DecidableEq E]
  {State : E→Type*} [∀ e,Fintype (State e)]

def supportedIndicatorCount (T : Finset A) (state : (∀ e,State e)→A→Bool)
    (σ : ∀ e,State e) : ℝ := ∑ a∈T,if state σ a=true then 1 else 0

theorem supportedIndicatorCount_pattern (T : Finset A) (state : (∀ e,State e)→A→Bool) (σ : ∀ e,State e) :
    supportedIndicatorCount T state σ=
      supportedPatternSum (fun a : A=>{a}) (fun a=>if a∈T then 1 else 0) (fun _ _=>true) state σ := by
  simp only [supportedIndicatorCount,supportedPatternSum,patternValue,Finset.prod_singleton]
  simp only [ite_mul,one_mul,zero_mul]
  symm
  rw [← Finset.sum_filter]
  simp
  convert Finset.sum_boole (R:=ℝ) (fun a : A=>state σ a=true) T using 1
  apply Finset.sum_congr rfl
  intro a ha
  by_cases h : state σ a=true <;> simp only [h,ite_true,ite_false]

theorem supportedIndicatorCount_expectation (μ : ∀ e,FiniteLaw (State e)) (T : Finset A)
    (state : (∀ e,State e)→A→Bool) :
    (FiniteLaw.pi μ).expectation (supportedIndicatorCount T state)=
      ∑ a∈T,(FiniteLaw.pi μ).probability (fun σ=>state σ a=true) := by
  unfold FiniteLaw.expectation supportedIndicatorCount FiniteLaw.probability
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro σ hσ
  split_ifs <;> simp

theorem supportedIndicatorCount_tail (μ : ∀ e,FiniteLaw (State e))
    (T : Finset A) (S : A→Finset E) (state : (∀ e,State e)→A→Bool)
    (hs : ∀ a σ τ,(∀ e∈S a,σ e=τ e) → state σ a=state τ a)
    (B : ℝ) (hB : 0<B) (hn : 0<Fintype.card A)
    (hread : ∀ a,((S a).card:ℝ)≤B)
    (haffect : ∀ e,((Finset.univ.filter (fun a=>e∈S a)).card:ℝ)≤B)
    (t : ℝ) (ht : 0<t) :
    (FiniteLaw.pi μ).probability (fun σ=>t≤
      |supportedIndicatorCount T state σ-(FiniteLaw.pi μ).expectation (supportedIndicatorCount T state)|)≤
      2*Real.exp (-2*t^2/(B^2*Fintype.card A)) := by
  have he : supportedIndicatorCount T state=
      supportedPatternSum (fun a : A=>{a}) (fun a=>if a∈T then 1 else 0) (fun _ _=>true) state :=
    funext (supportedIndicatorCount_pattern T state)
  rw [he]
  apply supportedPatternSum_tail μ (fun a : A=>{a}) (fun a=>if a∈T then 1 else 0)
    (by intro a;split_ifs <;> norm_num) (fun _ _=>true) S state hs B (Fintype.card A) hB
    (Nat.cast_pos.mpr hn) hread haffect
  · have hsum : ∀ a : A,(∑ i : A,if a∈({i}:Finset A) then (if i∈T then (1:ℝ) else 0) else 0)=
        if a∈T then 1 else 0 := by intro a;simp [eq_comm]
    simp only [hsum]
    calc
      _ ≤ ∑ a : A,(1:ℝ) := Finset.sum_le_sum (fun a _=>by split_ifs <;> norm_num)
      _ = _ := by simp
  · exact ht

end Oberwolfach
