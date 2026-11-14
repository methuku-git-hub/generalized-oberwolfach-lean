module

public import Oberwolfach.SupportedIndicatorScale

@[expose] public section

/-! Concentration of a set specified by local coordinate predicates.
The supplied ambient scale also covers an empty counting domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A E:Type*} [Fintype A] [Fintype E] [DecidableEq A] [DecidableEq E]
  {State:E→Type*} [∀ e,Fintype (State e)]

theorem finiteLaw_local_filter_tail (μ:∀ e,FiniteLaw (State e))
    (P:(∀ e,State e)→A→Prop) (S:A→Finset E)
    (hs:∀ a σ τ,(∀ e∈S a,σ e=τ e)→(P σ a↔P τ a))
    (B n:ℝ) (hB:0<B) (hn:0<n) (hsize:(Fintype.card A:ℝ)≤n)
    (hread:∀ a,((S a).card:ℝ)≤B)
    (haffect:∀ e,((Finset.univ.filter (fun a=>e∈S a)).card:ℝ)≤B)
    (t:ℝ) (ht:0<t):
    (FiniteLaw.pi μ).probability (fun σ=>t≤
      |((Finset.univ.filter (P σ)).card:ℝ)-
        (FiniteLaw.pi μ).expectation (fun τ=>((Finset.univ.filter (P τ)).card:ℝ))|)≤
      2*Real.exp (-2*t^2/(B^2*n)) := by
  let state: (∀ e,State e)→A→Bool:=fun σ a=>decide (P σ a)
  have he (σ:∀ e,State e):supportedIndicatorCount Finset.univ state σ=
      ((Finset.univ.filter (P σ)).card:ℝ) := by
    simp only [supportedIndicatorCount,state,decide_eq_true_eq]
    exact Finset.sum_boole (R:=ℝ) (P σ) Finset.univ
  have hh:=supportedIndicatorCount_tail_at_scale μ Finset.univ S state
    (fun a σ τ hagree=>by dsimp [state];rw [propext (hs a σ τ hagree)])
    B n hB hn hsize hread haffect t ht
  have hef:supportedIndicatorCount Finset.univ state=
      (fun σ=>((Finset.univ.filter (P σ)).card:ℝ)):=funext he
  simpa only [hef] using hh

end Oberwolfach
