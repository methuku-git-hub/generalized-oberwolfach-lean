module

public import Oberwolfach.LongReferenceMatchingThresholds
public import Oberwolfach.SharedVortexOrderedSize

@[expose] public section
/-! The vortex tolerance can meet the geometry and matching caps at once. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
universe b c d

theorem long_matching_geometry_beta_choice
    (αRef βMatch βParent εBal εRef κ x:ℝ)
    (hα:0<αRef) (hM:0<βMatch) (hP:0<βParent) (hBal:0<εBal)
    (hRef:0<εRef) (hκ:0<κ) (hx:0<x):
    ∃ βQ:ℝ,0<βQ ∧ βQ≤1/4 ∧ βQ≤αRef/4 ∧
      βQ≤βMatch ∧ βQ≤βParent ∧ βQ≤εBal/4 ∧ βQ≤εRef/4 ∧
      βQ≤κ ∧ βQ≤x ∧ βQ≤3*(2*αRef)/40 ∧ βQ≤3/20 := by
  let cap:=min βMatch (min κ (min x (min (3*(2*αRef)/40) (3/20))))
  have hc:0<cap:=by dsimp [cap];positivity
  obtain ⟨β,hβ,hquarter,hαcap,hcap,hparent,hbal,href,_⟩:=
    long_reference_matching_vortex_thresholds αRef cap βParent εBal εRef hα hc hP hBal hRef
  have hMcap:cap≤βMatch:=by dsimp [cap];exact min_le_left _ _
  have hκcap:cap≤κ:=by dsimp [cap];exact (min_le_right _ _).trans (min_le_left _ _)
  have hxcap:cap≤x:=by dsimp [cap];exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hgeomcap:cap≤3*(2*αRef)/40:=by dsimp [cap];exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hconstcap:cap≤3/20:=by dsimp [cap];exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  exact ⟨β,hβ,hquarter,hαcap,hcap.trans hMcap,hparent,hbal,href,hcap.trans hκcap,hcap.trans hxcap,hcap.trans hgeomcap,hcap.trans hconstcap⟩

/-- Choose the tolerance and a common size before the host order. -/
theorem long_matching_geometry_shared_vortex
    (αRef βMatch βParent εBal εRef κ x εQ ρ₀:ℝ)
    (hα:0<αRef) (hM:0<βMatch) (hP:0<βParent) (hBal:0<εBal)
    (hRef:0<εRef) (hκ:0<κ) (hx:0<x) (he:0<εQ) (heq:εQ<1/4) (hρ:0<ρ₀)
    (h:ℕ):
    ∃ βQ:ℝ,0<βQ ∧ βQ≤1/4 ∧ βQ≤αRef/4 ∧
      βQ≤βMatch ∧ βQ≤βParent ∧ βQ≤εBal/4 ∧ βQ≤εRef/4 ∧
      βQ≤κ ∧ βQ≤x ∧ βQ≤3*(2*αRef)/40 ∧ βQ≤3/20 ∧
    ∀ mMatch mGeom:ℕ, ∃ m:ℕ,1≤m ∧ mMatch≤m ∧ mGeom≤m ∧
      ∀ Nhost:ℕ, ∀ (V:Type b) [Fintype V] (A:Type c) [Nonempty A]
        (U:A→Type d) [∀a,Fintype (U a)] (G:SimpleGraph V) (D:ℕ),
      G.IsRegularOfDegree D → (Fintype.card V:ℝ)/2≤D →
      (∀a,ρ₀ ≤ initialIndexDensity (U a) D) →
      (∀a,initialIndexDensity (U a) D≤1) →
      max m Nhost≤Fintype.card V →
      ∃ Q:∀a,Vortex (U a) G D βQ εQ m, ∃π:Equiv.Perm V,
        (∀a i y,π y∈(Q a).extendedVertices i ↔ y∈(Q a).extendedVertices i) ∧
        (∀a b,(Q a).toVertexVortex=(Q b).toVertexVortex) ∧
        (∀y k,0<k→k<h→(π^k) y≠y) := by
  obtain ⟨β,hβ,h1,hαcap,hMc,hPc,hBc,hRc,hκc,hxc,hgeo,hconst⟩:=
    long_matching_geometry_beta_choice αRef βMatch βParent εBal εRef κ x hα hM hP hBal hRef hκ hx
  refine ⟨β,hβ,h1,hαcap,hMc,hPc,hBc,hRc,hκc,hxc,hgeo,hconst,?_⟩
  intro mMatch mGeom
  obtain ⟨m₀,hm₀,hv⟩:=shared_vortex_with_permutation_exists.{b,c,d} hβ he heq hρ h
  let m:=max m₀ (max mMatch mGeom)
  refine ⟨m,by dsimp [m];omega,by dsimp [m];omega,by dsimp [m];omega,?_⟩
  intro Nhost V _ A _ U _ G D hreg hD hlo hhi hn
  exact hv V A U G D m hreg hD hlo hhi (by dsimp [m];omega) (by omega)
end Oberwolfach
