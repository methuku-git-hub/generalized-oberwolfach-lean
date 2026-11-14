module

public import Oberwolfach.TwoStageEvents
public import Oberwolfach.ProductFailureBounds
public import Oberwolfach.FiniteLawIntersectionLower

@[expose] public section
/-! Attach an event that is likely conditional on the earlier state, without
charging the earlier failure probability twice. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_attach_conditional_event {Ω:Type} [Fintype Ω]
    {Γ:Ω→Type} [∀ω,Fintype (Γ ω)] (μ:FiniteLaw Ω) (ν:∀ω,FiniteLaw (Γ ω))
    (E:Ω→Prop) (A:(Σω,Γ ω)→Prop) (S:∀ω,Γ ω→Prop) (e δ:ℝ)
    (hδ:0≤δ) (hA:1-e≤(μ.sigma ν).probability A)
    (hAE:∀z,A z→E z.1)
    (hS:∀ω,E ω→1-δ≤(ν ω).probability (S ω)):
    1-(e+δ)≤(μ.sigma ν).probability (fun z=>A z∧S z.1 z.2):=by
  let B:=fun z:(Σω,Γ ω)=>¬E z.1∨S z.1 z.2
  have hc:∀ω,True→1-δ≤(ν ω).probability (fun x=>¬E ω∨S ω x):=by
    intro ω _
    by_cases he:E ω
    · simpa only [he,not_true_eq_false,false_or] using hS ω he
    · have hp:(ν ω).probability (fun x=>¬E ω∨S ω x)=1:=by
        simp [he,FiniteLaw.probability,(ν ω).total]
      linarith only [hp,hδ]
  have ht:=finiteLaw_twoStage_survival μ ν (fun _=>True) (fun ω x=>¬E ω∨S ω x) δ hc
  have htrue:μ.probability (fun _=>True)=1:=by simp [FiniteLaw.probability,μ.total]
  have hb:1-δ≤(μ.sigma ν).probability B:=by simpa only [htrue,mul_one,true_and] using ht
  have hi:=finiteLaw_intersection_lower (μ.sigma ν) A B e δ hA hb
  have hm:(μ.sigma ν).probability (fun z=>A z∧B z)≤
      (μ.sigma ν).probability (fun z=>A z∧S z.1 z.2):=by
    apply finiteLaw_probability_mono
    intro z hz
    refine ⟨hz.1,?_⟩
    exact hz.2.resolve_left (fun hn=>hn (hAE z hz.1))
  linarith only [hi,hm]
end Oberwolfach
