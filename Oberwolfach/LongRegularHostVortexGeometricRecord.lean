module

public import Oberwolfach.LongRegularHostVortex
public import Oberwolfach.MarkedVortexGeometricRecordEvent

@[expose] public section
/-! The regular-host vortex carries its uniform geometric records. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_regular_host_vortex_with_geometric_record
    (α β ε ρ₀ κ hcut ξ xiDeep ω x:ℝ) (N NI d:ℕ)
    (hN:1≤N) (hα:0<α) (hρ:0<ρ₀) (hβ:0<β)
    (he:0<ε) (he8:ε≤1/8) (heα:ε≤α/8) (heκ:ε≤κ)
    (hecut:ε≤hcut) (heξ:4*ε≤ξ) (hedeep:ε^2≤xiDeep)
    (hω:0≤ω) (hωv:ω≤ε/8) (hωu:ω≤ρ₀*ε/64)
    (hb1:β≤1/4) (hbα:β≤α/8) (hbα':β≤3*α/40) (hb':β≤3/20)
    (hbκ:β≤κ) (hbx:β≤x):
    ∃m₀:ℕ,1≤m₀ ∧ ∀(Allowed:Set ℕ),Allowed.Nonempty→(∀r∈Allowed,3≤r)→
    ∀n:ℕ,0<n→∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n)) (D m:ℕ),
      G.IsRegularOfDegree D→(allowedThreshold Allowed+α)*n≤(D:ℝ)→
      ρ₀ ≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤m→m≤n→
      ∃Q:Vortex U G D β ε m,∃π:Equiv.Perm (Fin n),
        (∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i) ∧
        (∀v l,0<l→l<2*d+1→(π^l) v≠v) ∧
        ∀L:ℕ,L<Q.length→MarkedVortexGeometricRecordEvent Q α ρ₀ κ hcut ξ xiDeep ω x N NI L := by
  have he1:ε<1/4:=by linarith
  obtain ⟨mV,hmV,hvortex⟩:=long_regular_host_vortex_with_permutation α β ε ρ₀ hα hβ he he1 hρ d
  obtain ⟨mG,hmG,hgeo⟩:=marked_vortex_uniform_geometric_record_event α ρ₀ ε κ hcut ξ xiDeep ω x N NI
    hN hα hρ he he8 heα heκ hecut heξ hedeep hω hωv hωu
  refine ⟨max mV mG,le_trans hmV (Nat.le_max_left _ _),?_⟩
  intro Allowed hAllowed hvalid n hn U _ G D m hreg hmin hρlo hρhi hm hmn
  obtain ⟨Q,π,hpres,hshort⟩:=hvortex Allowed hAllowed hvalid n hn U G D m hreg hmin hρlo hρhi (by omega) hmn
  letI : DecidableEq U:=Classical.decEq U
  have hnum:=long_regular_host_numeric_inputs n D hn U Allowed hAllowed hvalid α hα G hreg hmin
  refine ⟨Q,π,hpres,hshort,?_⟩
  intro L hL
  exact hgeo (Fin n) U G D m β Q hreg (by simpa using hn) (by simpa using hnum.2.2.2.1)
    hρlo hρhi hβ.le hb1 hbα hbα' hb' hbκ hbx (by omega) L hL
end Oberwolfach
