module

public import Oberwolfach.MarkedReferenceActiveEndpointBase

@[expose] public section
/-! The reference statistics and cut families at every parent level,
before deletion, on the same retained sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]

theorem marked_reference_parent_base
    (r h d:ℕ) (α βconfig εref δref tol ζActive ζAbs tstar εAbs:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (s₀ p k:ℝ) (hα:0≤α) (hp:0≤p) (hk:0≤k) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (hevent:MarkedReferenceActiveAbsorberProperty r h d α βconfig εref δref tol ζActive ζAbs tstar εAbs
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p k q s a j z):
    ∀ i≤L,
      let W:=markedVortexVertexType Q i
      let Z:=markedVortexHubType Q i
      let f:=markedVortexVertexEmbedding Q i
      let g:=markedVortexHubEmbedding Q i
      let ρ:=markedVortexPermutation Q π hpres i
      let Dload:=2*(Fintype.card Z:ℝ)/initialIndexDensity U D
      let ω:=rawMarkedRestrictPair f g z.1;
      MarkedReferenceStatistics (G.comap f) ρ d a j Dload εref δref (α/4) p k s₀ (s₀/((r+4:ℕ):ℝ)) ω ∧
      MarkedReferenceCutFamilies (G.comap f) ρ d a j (α/4) p k tstar ω:=by
  intro i hi W Z f g ρ Dload ω
  have hh:=(hevent.1.1 i hi).2 0 (by norm_num)
    (by
      have hh:0≤(3/4:ℝ)*(α/2)*p^2:=by positivity
      linarith only [hh])
    (by
      have hm:0≤min p k:=le_min hp hk
      have hh:0≤(α/2)*min p k/8:=by positivity
      linarith only [hh])
    (⊥:SimpleGraph W) (by intro x;simp)
  have heq:α/2/2=α/4:=by ring
  simpa only [graph_bottom_edgeFinset_any_instance,rawMarkedDeleteRims_empty,add_zero,heq] using hh
end Oberwolfach
