module

public import Oberwolfach.MarkedTerminalVortexGeometricRecord

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_named_host_terminal_geometry
    (αRef ρ₀ εQ εMax κmax hcut ξ xiDeep ω x:ℝ) (N NI:ℕ)
    (hN:1≤N) (hα:0<αRef) (hρ₀:0<ρ₀) (he:0<εQ) (heMax:εQ≤εMax)
    (hMax8:εMax≤1/8) (hMaxAlpha:εMax≤(2*αRef)/8)
    (hMaxκ:εMax≤κmax) (hMaxcut:εMax≤hcut) (hMaxξ:4*εMax≤ξ)
    (hedeep:εQ^2≤xiDeep) (hω:0≤ω) (hωv:ω≤εQ/8) (hωu:ω≤ρ₀*εQ/64):
    ∃ m₀:ℕ,1≤m₀ ∧
    ∀ (V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (G:SimpleGraph V) (D m:ℕ) (β:ℝ) (Q:Vortex U G D β εQ m),
      G.IsRegularOfDegree D → 0<Fintype.card V →
      (1/2+2*αRef)*Fintype.card V≤(D:ℝ) →
      ρ₀ ≤ initialIndexDensity U D → initialIndexDensity U D≤1 →
      0≤β → β≤1/4 → β≤(2*αRef)/8 → β≤3*(2*αRef)/40 → β≤3/20 → β≤κmax → β≤x → m₀≤m →
      MarkedVortexGeometricRecordEvent Q (2*αRef) ρ₀ κmax hcut ξ xiDeep ω x N NI (Q.length-1) := by
  obtain ⟨m₀,hm₀,hGeo⟩:=marked_vortex_terminal_geometric_record
    (2*αRef) ρ₀ εQ κmax hcut ξ xiDeep ω x N NI hN (by positivity) hρ₀ he
      (heMax.trans hMax8) (heMax.trans hMaxAlpha) (heMax.trans hMaxκ) (heMax.trans hMaxcut)
      (by linarith) hedeep hω hωv hωu
  refine ⟨m₀,hm₀,?_⟩
  intro V U _ _ _ _ G D m β Q hreg hn hD hlo hhi hb hb1 hba hbas hb3 hbκ hbx hm
  obtain ⟨L,hL,hLength,hG⟩:=hGeo V U G D m β Q hreg hn hD hlo hhi hb hb1 hba hbas hb3 hbκ hbx hm
  have hEq:L=Q.length-1:=by omega
  simpa [hEq] using hG
end Oberwolfach
