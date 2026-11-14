module

public import Oberwolfach.MarkedReferenceParameterNormalization

@[expose] public section
/-! Reference statistics and cut inputs with the exact level-record density,
cycle and margin normalizations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]

theorem marked_vortex_reference_record_inputs
    (r h d:ℕ) (α βconfig κ tol ζActive ζAbs tstar εAbs:ℝ)
    (hα:0≤α)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (s₀:ℝ) (hs₀:0≤s₀) (hρ:0 ≤ initialIndexDensity U D)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (hevent:MarkedReferenceActiveAbsorberProperty r h d (α/2) βconfig (κ/4) κ tol ζActive ζAbs tstar εAbs
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ (initialIndexDensity U D*s₀/2)
      ((initialIndexDensity U D*s₀/2)/((r+4:ℕ):ℝ)) q s a j z):
    ∀ i≤L,
      let W:=markedVortexVertexType Q i
      let Z:=markedVortexHubType Q i
      let f:=markedVortexVertexEmbedding Q i
      let g:=markedVortexHubEmbedding Q i
      let ρ:=markedVortexPermutation Q π hpres i
      let rho:=initialIndexDensity U D
      let c:ℝ:=(r+4:ℕ)
      let t:=s₀/c
      let pRef:=rho*c*t/2
      let kRef:=pRef/c
      let DRef:=2*(Fintype.card Z:ℝ)/rho
      let σ:=rawMarkedRestrictPair f g z.1;
      MarkedReferenceStatistics (G.comap f) ρ d a j DRef (κ/4) κ (2*(α/16)) pRef kRef (c*t) t σ ∧
      MarkedReferenceCutFamilies (G.comap f) ρ d a j (2*(α/16)) pRef kRef tstar σ:=by
  intro i hi W Z f g ρ rho c t pRef kRef DRef σ
  have hc:0<c:=by dsimp [c];positivity
  have hp:0 ≤ initialIndexDensity U D*s₀/2:=by positivity
  have hk:0≤(initialIndexDensity U D*s₀/2)/((r+4:ℕ):ℝ):=by positivity
  have hh:=marked_reference_parent_base r h d (α/2) βconfig (κ/4) κ tol ζActive ζAbs tstar εAbs
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ (initialIndexDensity U D*s₀/2)
    ((initialIndexDensity U D*s₀/2)/((r+4:ℕ):ℝ)) (by positivity) hp hk q s a j z hevent i hi
  have ht:c*t=s₀:=by dsimp [t];field_simp
  have hpRef:pRef=initialIndexDensity U D*s₀/2:=by dsimp [pRef,rho];rw [mul_assoc,ht]
  have hkRef:kRef=(initialIndexDensity U D*s₀/2)/((r+4:ℕ):ℝ):=by dsimp [kRef,c];rw [hpRef]
  have hgamma:(α/2)/4=2*(α/16):=by ring
  simpa only [hpRef,hkRef,ht,hgamma] using hh
end Oberwolfach
