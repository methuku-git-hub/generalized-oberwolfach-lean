module

public import Oberwolfach.OrdinaryTriangleNumericCoreThresholdSelection

@[expose] public section
/-! A single larger terminal and host threshold can be used by the wheel
certificate and the other pre-host choices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_numeric_core_threshold_monotone
    (β ε ρ₀ α pmin εrows tpot lamInner:ℝ) (d k:ℕ)
    (ω βout b Bweight hpack δpack εstar cLinear bHub BHub ηhub:ℝ)
    (p βeGeo βhGeo ν cap τ eps ellCap:ℝ) (Msmall vsmall Mlarge vlarge:ℕ)
    (hM:Msmall≤Mlarge) (hv:vsmall≤vlarge)
    (hcert:OrdinaryTriangleNumericCoreAfterThreshold β ε ρ₀ α pmin εrows tpot lamInner d k
      ω βout b Bweight hpack δpack εstar cLinear bHub BHub ηhub p βeGeo βhGeo ν cap τ eps ellCap Msmall vsmall):
    OrdinaryTriangleNumericCoreAfterThreshold β ε ρ₀ α pmin εrows tpot lamInner d k
      ω βout b Bweight hpack δpack εstar cLinear bHub BHub ηhub p βeGeo βhGeo ν cap τ eps ellCap Mlarge vlarge :=by
  intro n q D mv P hreg hn hD hρlo hρhi hvlarge hterminal
  have hMreal:(Msmall:ℝ)≤Mlarge:=by exact_mod_cast hM
  exact hcert n q D mv P hreg hn hD hρlo hρhi (hv.trans hvlarge) (hMreal.trans hterminal)
end Oberwolfach
