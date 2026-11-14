module

public import Oberwolfach.SupportedIndicatorCounts

@[expose] public section

/-! A fixed-domain indicator count at a supplied ambient scale. The domain
may be empty; positivity is required only of the ambient scale. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A E : Type*} [Fintype A] [Fintype E] [DecidableEq A] [DecidableEq E]
  {State : E→Type*} [∀ e,Fintype (State e)]

theorem supportedIndicatorCount_tail_at_scale (μ : ∀ e,FiniteLaw (State e))
    (T : Finset A) (S : A→Finset E) (state : (∀ e,State e)→A→Bool)
    (hs : ∀ a σ τ,(∀ e∈S a,σ e=τ e) → state σ a=state τ a)
    (B n : ℝ) (hB : 0<B) (hn : 0<n) (hsize : (Fintype.card A:ℝ)≤n)
    (hread : ∀ a,((S a).card:ℝ)≤B)
    (haffect : ∀ e,((Finset.univ.filter (fun a=>e∈S a)).card:ℝ)≤B)
    (t : ℝ) (ht : 0<t) :
    (FiniteLaw.pi μ).probability (fun σ=>t≤
      |supportedIndicatorCount T state σ-(FiniteLaw.pi μ).expectation (supportedIndicatorCount T state)|)≤
      2*Real.exp (-2*t^2/(B^2*n)) := by
  have he : supportedIndicatorCount T state=
      supportedPatternSum (fun a : A=>{a}) (fun a=>if a∈T then 1 else 0) (fun _ _=>true) state :=
    funext (supportedIndicatorCount_pattern T state)
  rw [he]
  apply supportedPatternSum_tail μ (fun a : A=>{a}) (fun a=>if a∈T then 1 else 0)
    (by intro a;split_ifs <;> norm_num) (fun _ _=>true) S state hs B n hB hn hread haffect
  · have hsum : ∀ a : A,(∑ i : A,if a∈({i}:Finset A) then (if i∈T then (1:ℝ) else 0) else 0)=
        if a∈T then 1 else 0 := by intro a;simp [eq_comm]
    simp only [hsum]
    calc
      _ ≤ ∑ a : A,(1:ℝ) := Finset.sum_le_sum (fun a _=>by split_ifs <;> norm_num)
      _ = Fintype.card A := by simp
      _ ≤ n := hsize
  · exact ht

end Oberwolfach
