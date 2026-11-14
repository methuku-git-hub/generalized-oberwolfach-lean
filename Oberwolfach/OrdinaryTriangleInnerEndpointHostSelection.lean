module

public import Oberwolfach.OrdinaryTriangleInnerEndpointHostData

@[expose] public section
/-! The common-event selector chooses a host threshold before the graph,
while keeping the pointwise sampling-law attachment named and separate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryTriangleInnerEndpointHostSelector
    (α c C ε ρ₀ pmin ξ b Bweight ηHub Kdom eParent hParent cap χ χend tpot:ℝ)
    (d:ℕ) (hd:2≤d) (β:ℝ) (v₀:ℕ):Prop :=
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U],
    ∀(P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D  →  0<Fintype.card V  → 
      ρ₀ ≤ initialIndexDensity U D  →  initialIndexDensity U D ≤ 1  →  v₀ ≤ vsize  → 
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      (∀x l,0<l  →  l<2*d+1  →  (π^l) x≠x)  → 
    ∀(θhost p k p₂ k₂ u:ℝ) (hθ:1/2 ≤ θhost) (hthreshold:cycleThreshold 3 ≤ θhost)
      (hdegree:(θhost+α)*Fintype.card V ≤ D)
      (hp:0 ≤ p) (hk:0 ≤ k) (hp₂:0 ≤ p₂) (hk₂:0 ≤ k₂) (hu:0 ≤ u) (hsum:2*p+2*k+2*p₂+2*k₂+u ≤ 1),
    ∀(pH:ℝ),pmin ≤ 2*p  →  2*p ≤ 1  →  pmin ≤ pH  →  pH ≤ 1  →  2*p=initialIndexDensity U D*pH  → 
    OrdinaryTriangleInnerEndpointHostData (Γ:=Γ) (Color:=Color) β ε P D vsize Q π hπ d hd
      p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH c C pmin ξ b Bweight ηHub Kdom eParent hParent cap χ χend tpot

theorem ordinary_triangle_inner_endpoint_select_host_data
    (α c C ε ρ₀ pmin ξ b Bweight ηHub Kdom eParent hParent cap:ℝ)
    (hsetup:OrdinaryTriangleInnerEndpointAfterSetup α c C ε ρ₀ pmin ξ b Bweight ηHub Kdom eParent hParent cap)
    (χ:ℝ) (hχ:0<χ) (d:ℕ) (hd:2≤d) (β:ℝ)
    (hβ:0≤β) (hβ1:β≤1/4) (hβα:β≤α/8) (hgap:ξ+2*β<ηHub)
    (tpot χend:ℝ) (htpot:0<tpot) (hχend:0<χend):
    ∃v₀:ℕ,1≤v₀ ∧ OrdinaryTriangleInnerEndpointHostSelector
      α c C ε ρ₀ pmin ξ b Bweight ηHub Kdom eParent hParent cap χ χend tpot d hd β v₀ :=by
  obtain ⟨v₀,hv₀,hattach⟩:=hsetup χ hχ d hd β hβ hβ1 hβα hgap tpot χend htpot hχend
  exact ⟨v₀,hv₀,hattach⟩
end Oberwolfach
