module

public import Oberwolfach.OrdinaryTriangleCommonCertificateSizeChoice
public import Oberwolfach.OrdinaryTriangleVortexSizeForCertificates

@[expose] public section
/-! Choose the common wheel and vortex sizes after every local threshold,
and before the host, absorber support, or sample are selected. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_wheel_vortex_sizes_before_sample
    (β ε ρ₀ α pmin εrows tpot lamInner:ℝ) (d k:ℕ)
    (ω βout b Bweight hpack δpack εstar cLinear bHub BHub ηhub:ℝ)
    (p βeGeo βhGeo ν cap τ eps ellCap ηBudget:ℝ)
    (Msmall vCert N₀ Ncert Nedit vOuter vInner mAll Mhost Mcut:ℕ)
    (hβ:0<β) (hε:0<ε) (hεsmall:ε<1/4) (hρ:0<ρ₀) (hη:0<ηBudget)
    (hcert:OrdinaryTriangleNumericCoreAfterThreshold β ε ρ₀ α pmin εrows tpot lamInner d k
      ω βout b Bweight hpack δpack εstar cLinear bHub BHub ηhub p βeGeo βhGeo ν cap τ eps ellCap Msmall vCert):
    ∃M vCommon mVortex mv:ℕ,
      1≤M ∧ Msmall≤M ∧ N₀≤M ∧ Ncert≤M ∧ Nedit≤M ∧ 2/ε≤(M:ℝ) ∧
      (∀n:ℕ,M≤n→∀cost:ℝ,cost≤14*ηBudget*n→cost+2*((3*d:ℕ):ℝ)≤15*ηBudget*n) ∧
      vCert≤vCommon ∧ vOuter≤vCommon ∧ vInner≤vCommon ∧ mAll≤vCommon ∧
      1≤mv ∧ vCommon≤mv ∧ mVortex≤mv ∧
      (M:ℝ)≤ε*mv/2 ∧ (Mhost:ℝ)≤ε*mv/2 ∧ (Mcut:ℝ)≤ε*mv/2 ∧
      OrdinaryLookbackVortexAt β ε ρ₀ d mVortex ∧
      OrdinaryTriangleNumericCoreAfterThreshold β ε ρ₀ α pmin εrows tpot lamInner d k
        ω βout b Bweight hpack δpack εstar cLinear bHub BHub ηhub p βeGeo βhGeo ν cap τ eps ellCap M vCommon :=by
  obtain ⟨M,vCommon,hM,hSmall,hN₀,hNcert,hNedit,htwo,hmatch,hvCert,hvOuter,hvInner,hmAll,hcert',hlevels⟩:=
    ordinary_triangle_common_certificate_size_choice β ε ρ₀ α pmin εrows tpot lamInner d k
      ω βout b Bweight hpack δpack εstar cLinear bHub BHub ηhub p βeGeo βhGeo ν cap τ eps ellCap ηBudget
      Msmall vCert N₀ Ncert Nedit vOuter vInner mAll hε hρ hη hcert
  obtain ⟨mVortex,mv,hmv,hCommon,hVortex,hterm,hhost,hcut,hlook⟩:=
    ordinary_triangle_vortex_size_for_certificates β ε ρ₀ d M vCommon Mhost Mcut hβ hε hεsmall hρ
  exact ⟨M,vCommon,mVortex,mv,hM,hSmall,hN₀,hNcert,hNedit,htwo,hmatch,hvCert,hvOuter,hvInner,hmAll,
    hmv,hCommon,hVortex,hterm,hhost,hcut,hlook,hcert'⟩
end Oberwolfach
