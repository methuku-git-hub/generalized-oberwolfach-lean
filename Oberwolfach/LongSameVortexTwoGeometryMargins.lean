module

public import Oberwolfach.MarkedVortexGeometricRecordEvent

@[expose] public section
/-! Construct both geometric margins for the same given vortex. This aligns
an alphaRef-level chain with a parent event using 2*alphaRef. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_same_vortex_two_geometry_margins
    (αRef ρ₀ ε κ hcut ξ xiDeep ω x:ℝ) (N NI:ℕ)
    (hN:1≤N) (hα:0<αRef) (hρ₀:0<ρ₀) (hε:0<ε) (hε8:ε≤1/8)
    (hεα:ε≤αRef/8) (hεκ:ε≤κ) (hεcut:ε≤hcut) (hεξ:4*ε≤ξ) (hεdeep:ε^2≤xiDeep)
    (hω:0≤ω) (hωv:ω≤ε/8) (hωu:ω≤ρ₀*ε/64):
    ∃v₀:ℕ,1≤v₀ ∧
    ∀ (V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (G:SimpleGraph V) (D vsize:ℕ) (β:ℝ) (Q:Vortex U G D β ε vsize),
      G.IsRegularOfDegree D→0<Fintype.card V→
      (1/2+2*αRef)*Fintype.card V≤(D:ℝ)→
      ρ₀ ≤ initialIndexDensity U D→initialIndexDensity U D≤1→
      0≤β→β≤1/4→β≤αRef/8→β≤3*αRef/40→β≤3/20→β≤κ→β≤x→v₀≤vsize→
      ∀L:ℕ,L<Q.length→
      MarkedVortexGeometricRecordEvent Q αRef ρ₀ κ hcut ξ xiDeep ω x N NI L ∧
      MarkedVortexGeometricRecordEvent Q (2*αRef) ρ₀ κ hcut ξ xiDeep ω x N NI L := by
  obtain ⟨v₁,hv₁,hgeo₁⟩:=marked_vortex_uniform_geometric_record_event αRef ρ₀ ε κ hcut ξ xiDeep ω x N NI
    hN hα hρ₀ hε hε8 hεα hεκ hεcut hεξ hεdeep hω hωv hωu
  obtain ⟨v₂,hv₂,hgeo₂⟩:=marked_vortex_uniform_geometric_record_event (2*αRef) ρ₀ ε κ hcut ξ xiDeep ω x N NI
    hN (by linarith) hρ₀ hε hε8 (by linarith) hεκ hεcut hεξ hεdeep hω hωv hωu
  refine ⟨max v₁ v₂,by omega,?_⟩
  intro V U _ _ _ _ G D vsize β Q hreg hn hdegree hρlo hρhi hβ hβ1 hβα hβa hβ20 hβκ hβx hv L hL
  have hn0:0≤(Fintype.card V:ℝ):=by positivity
  have hdegree₁:(1/2+αRef)*Fintype.card V≤(D:ℝ):=by nlinarith
  refine ⟨hgeo₁ V U G D vsize β Q hreg hn hdegree₁ hρlo hρhi hβ hβ1 hβα hβa hβ20 hβκ hβx (by omega) L hL,?_⟩
  exact hgeo₂ V U G D vsize β Q hreg hn hdegree hρlo hρhi hβ hβ1 (by linarith) (by linarith) hβ20 hβκ hβx (by omega) L hL
end Oberwolfach
