module

public import Oberwolfach.GoodPlacementEvents
public import Oberwolfach.FiniteLawMap

@[expose] public section
/-! Combine the fixed-domain basic event with a projected reference event.
The projection may come from dependent retention, and no independence is used. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem class_reference_basic_budget {Ω R:Type} [Fintype Ω] [Fintype R]
    (μ:FiniteLaw Ω) (ref:FiniteLaw R) (f:Ω→R) (hf:μ.map f=ref)
    (Basic:Ω→Prop) (Reference:R→Prop) (χ:ℝ) (n:ℕ)
    (hχ:0≤χ) (hn:0<n)
    (hb:1-7/(n:ℝ)≤μ.probability Basic)
    (hr:1-(100*(χ/2)+100/(n:ℝ))≤ref.probability Reference):
    1-(100*χ+200/(n:ℝ))≤μ.probability (fun ω=>Basic ω ∧ Reference (f ω)):=by
  have hr':1-(100*(χ/2)+100/(n:ℝ))≤μ.probability (fun ω=>Reference (f ω)):=by
    rw [←finiteLaw_map_probability, hf]
    exact hr
  have h:=finiteLaw_good_intersection μ Basic (fun ω=>Reference (f ω)) (100*(χ/2)+100/(n:ℝ)) hr'
  have hnR:0≤(1:ℝ)/(n:ℝ):=by positivity
  have h7:(7:ℝ)/(n:ℝ)=7*(1/(n:ℝ)):=by ring
  have h100:(100:ℝ)/(n:ℝ)=100*(1/(n:ℝ)):=by ring
  have h200:(200:ℝ)/(n:ℝ)=200*(1/(n:ℝ)):=by ring
  linarith
end Oberwolfach
