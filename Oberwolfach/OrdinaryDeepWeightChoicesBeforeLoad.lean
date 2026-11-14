module

public import Oberwolfach.OrdinaryDeepUniformParameterChoices

@[expose] public section
/-! Select only the weight and domain bounds, retaining the load already
fixed by the common local-certificate hierarchy. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_weight_choices_before_load
    (m:ℕ) (a c capEdit ε ρ₀ pmin C:ℝ)
    (ha0:0<a) (hc:0<c) (hEdit:0<capEdit)
    (hε:0<ε) (hρ:0<ρ₀) (hp:0<pmin) (hC:0<C):
    ∃b Kdom Bweight:ℝ,0<b ∧ b≤c ∧ b≤capEdit ∧ 0<Kdom ∧ 0<Bweight ∧
      2/ε≤Kdom ∧ 1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom ∧
      (4*C/pmin^(3*m+1))*Kdom^m≤Bweight :=by
  obtain ⟨_,b,Kdom,Bweight,_,_,_,hb,hbc,hbcap,hK,hB,hK1,hK2,hweight⟩:=
    ordinary_deep_uniform_parameter_choices m a c (a/2) capEdit ε ρ₀ pmin C ha0 hc (by positivity) hEdit hε hρ hp hC
  exact ⟨b,Kdom,Bweight,hb,hbc,hbcap,hK,hB,hK1,hK2,hweight⟩
end Oberwolfach
