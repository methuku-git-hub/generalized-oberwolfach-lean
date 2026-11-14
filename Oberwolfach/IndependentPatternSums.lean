module

public import Oberwolfach.SupportedPatternSums
public import Oberwolfach.FinitePatternIncidence
public import Oberwolfach.ConditionalRealization

@[expose] public section

/-! Concentration for a fixed family of patterns in independent physical
trials, using its actual total weight and edge incidences. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem independent_pattern_sum_tail {A I : Type*} [Fintype A] [DecidableEq A] [Fintype I]
    {State : A → Type*} [∀ a,Fintype (State a)]
    (μ : ∀ a,FiniteLaw (State a)) (R : I → Finset A) (w : I → ℝ)
    (hw : ∀ i,0≤w i) (s : I → ∀ a,State a)
    (a q L : ℝ) (ha : 0<a) (hq : 0<q) (hL : 0<L)
    (hsize : ∀ i,((R i).card:ℝ)≤q) (htotal : (∑ i,w i)≤L)
    (hload : ∀ e,(∑ i,if e∈R i then w i else 0)≤a)
    (t : ℝ) (ht : 0<t) :
    (FiniteLaw.pi μ).probability (fun σ=>t≤
      |(∑ i,w i*patternValue (R i) (s i) σ)-
        (∑ i,w i*∏ e∈R i,(μ e).mass (s i e))|)≤
      2*Real.exp (-2*t^2/(a*q*L)) := by
  have hh := supportedPatternSum_tail μ R w hw s (fun e=>{e}) (fun σ=>σ)
    (by intro e σ τ h;exact h e (Finset.mem_singleton_self e))
    1 (a*q*L) (by norm_num) (by positivity)
    (by intro e;norm_num)
    (by
      intro e
      have he : Finset.univ.filter (fun b=>e∈({b}:Finset A))={e} := by ext b;simp [eq_comm]
      rw [he];norm_num)
    (finite_pattern_incidence_square_sum R w hw a q L ha.le hq.le hsize htotal hload) t ht
  have he := supportedPatternSum_expectation μ R w s (fun e=>{e}) (fun σ=>σ)
    (by intro e σ τ h;exact h e (Finset.mem_singleton_self e))
    (by intro i a ha b hb hab;simpa using hab)
  simp only [finiteLaw_pi_coordinate_probability] at he
  rw [he] at hh
  simpa only [supportedPatternSum,one_pow,one_mul] using hh

end Oberwolfach
