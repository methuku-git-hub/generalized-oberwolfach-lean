module

public import Oberwolfach.MarkedReferenceActiveAbsorberProperty

@[expose] public section
/-! Reference rim tolerance may be weakened without altering the sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]

omit [Nonempty V] in
theorem marked_reference_statistics_epsilon_mono
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (g:Γ) (j:Color)
    (D ε ε' δ γ p k s t:ℝ) (σ:RawMarkedOutcome V U Γ Color)
    (hε:ε≤ε') (h:MarkedReferenceStatistics P π d g j D ε δ γ p k s t σ):
    MarkedReferenceStatistics P π d g j D ε' δ γ p k s t σ := by
  refine ⟨⟨?_,h.1.2⟩,h.2⟩
  intro a x
  exact ⟨(h.1.1 a x).1.trans (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _)),
    (h.1.1 a x).2.trans (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _))⟩

theorem marked_reference_active_absorber_epsilon_mono
    (r h d:ℕ) (α βconfig εref εref' δref tol ζActive ζAbs tstar εAbs:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (s₀ p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (hε:εref≤εref')
    (hGood:MarkedReferenceActiveAbsorberProperty r h d α βconfig εref δref tol ζActive ζAbs tstar εAbs
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p k q s a j z):
    MarkedReferenceActiveAbsorberProperty r h d α βconfig εref' δref tol ζActive ζAbs tstar εAbs
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p k q s a j z := by
  rcases hGood with ⟨⟨hConfig,hRows⟩,hAbs⟩
  refine ⟨⟨?_,hRows⟩,hAbs⟩
  intro i hi
  obtain ⟨hcfg,hstats⟩:=hConfig i hi
  refine ⟨hcfg,?_⟩
  intro ζ hζ hgap hζcap DR hDR
  obtain ⟨hstat,hcut⟩:=hstats ζ hζ hgap hζcap DR hDR
  refine ⟨?_,hcut⟩
  exact marked_reference_statistics_epsilon_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (by linarith) hstat
end Oberwolfach
