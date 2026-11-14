module

public import Oberwolfach.FirstVortexJointReferenceGeometryBeta
public import Oberwolfach.MarkedVortexGeometricRecordEvent

@[expose] public section
/-! Choose one vortex parameter for the reference selector and obtain its
geometric record uniformly for every admissible host and every level. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_reference_geometry_instantiation
    (α ρ₀ ε κ hcut ξ xiDeep ω x βmax εBal εRef:ℝ) (N NI:ℕ)
    (hN:1≤N) (hα:0<α) (hρ₀:0<ρ₀) (he:0<ε) (he8:ε≤1/8) (heAlpha:ε≤α/8)
    (hκ:0<κ) (heκ:ε≤κ) (hecut:ε≤hcut) (heξ:4*ε≤ξ) (hedeep:ε^2≤xiDeep)
    (hω:0≤ω) (hωv:ω≤ε/8) (hωu:ω≤ρ₀*ε/64)
    (hx:0<x) (hβ:0<βmax) (hBal:0<εBal) (hRef:0<εRef):
    ∃β:ℝ,0<β ∧ β≤1/4 ∧ β≤α/8 ∧ β≤3*α/40 ∧ β≤3/20 ∧
      β≤κ ∧ β≤x ∧ β≤βmax ∧ β≤εBal/4 ∧ β≤εRef/4 ∧
    ∃m₀:ℕ,1≤m₀ ∧
      ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (G:SimpleGraph V) (D m:ℕ) (Q:Vortex U G D β ε m),
      G.IsRegularOfDegree D→0<Fintype.card V→
      (1/2+α)*Fintype.card V≤(D:ℝ)→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤m→
      ∀L:ℕ,L<Q.length→
        MarkedVortexGeometricRecordEvent Q α ρ₀ κ hcut ξ xiDeep ω x N NI L :=by
  obtain ⟨β,hβ0,hβquarter,hβα,hβαstrong,hβstrong,hβκ,hβx,hβmax,hβbal,hβref⟩:=
    first_vortex_joint_reference_geometry_beta α κ x βmax εBal εRef hα hκ hx hβ hBal hRef
  obtain ⟨m₀,hm₀,hGeo⟩:=marked_vortex_uniform_geometric_record_event α ρ₀ ε κ hcut ξ xiDeep ω x N NI
    hN hα hρ₀ he he8 heAlpha heκ hecut heξ hedeep hω hωv hωu
  refine ⟨β,hβ0,hβquarter,hβα,hβαstrong,hβstrong,hβκ,hβx,hβmax,hβbal,hβref,m₀,hm₀,?_⟩
  intro V U _ _ _ _ G D m Q hreg hn hD hρlo hρhi hm L hL
  exact hGeo V U G D m β Q hreg hn hD hρlo hρhi hβ0.le hβquarter hβα hβαstrong hβstrong hβκ hβx hm L hL
end Oberwolfach
