module

public import Oberwolfach.MarkedVortexGeometricRecordEvent

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_terminal_geometric_record
    (α ρ₀ ε κ hcut ξ xiDeep ω x:ℝ) (N NI:ℕ)
    (hN:1≤N) (hα:0<α) (hρ₀:0<ρ₀) (he:0<ε) (he8:ε≤1/8) (heAlpha:ε≤α/8)
    (heκ:ε≤κ) (hecut:ε≤hcut) (heξ:4*ε≤ξ) (hedeep:ε^2≤xiDeep)
    (hω:0≤ω) (hωv:ω≤ε/8) (hωu:ω≤ρ₀*ε/64):
    ∃ m₀:ℕ,1≤m₀ ∧
    ∀ (V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (G:SimpleGraph V) (D m:ℕ) (β:ℝ) (Q:Vortex U G D β ε m),
      G.IsRegularOfDegree D → 0<Fintype.card V →
      (1/2+α)*Fintype.card V≤(D:ℝ) →
      ρ₀ ≤ initialIndexDensity U D → initialIndexDensity U D≤1 →
      0≤β → β≤1/4 → β≤α/8 → β≤3*α/40 → β≤3/20 → β≤κ → β≤x → m₀≤m →
      ∃L:ℕ,L<Q.length ∧ L+1=Q.length ∧
        MarkedVortexGeometricRecordEvent Q α ρ₀ κ hcut ξ xiDeep ω x N NI L := by
  obtain ⟨m₀,hm₀,hGeo⟩:=marked_vortex_uniform_geometric_record_event α ρ₀ ε κ hcut ξ xiDeep ω x N NI
    hN hα hρ₀ he he8 heAlpha heκ hecut heξ hedeep hω hωv hωu
  refine ⟨m₀,hm₀,?_⟩
  intro V U _ _ _ _ G D m β Q hreg hn hD hρlo hρhi hb hb1 hbα hbαstrong hbstrong hbκ hbx hm
  have hlength:0<Q.length:=Q.length_pos
  refine ⟨Q.length-1,by omega,by omega,?_⟩
  exact hGeo V U G D m β Q hreg hn hD hρlo hρhi hb hb1 hbα hbαstrong hbstrong hbκ hbx hm (Q.length-1) (by omega)
end Oberwolfach
