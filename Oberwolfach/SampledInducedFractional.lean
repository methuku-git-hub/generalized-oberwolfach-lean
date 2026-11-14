module

public import Oberwolfach.SampledInducedDensity

@[expose] public section

/-! The successful sample supplies a genuine fractional cycle decomposition
by the proved ordinary threshold, before any averaging of coefficients. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem sampled_induced_fractional (r : ℕ) (hr : 3≤r) (α : ℝ) (hα : 0<α) :
    ∃ N : ℕ,∀ (V : Type) [Fintype V] [DecidableEq V],∀ m≥N,
      ∀ (G : SimpleGraph V) (z : FixedSubset V m × (Sym2 V → Bool)),
      sampledInducedDense G (cycleThreshold r) α z →
      HasFractionalDecomposition (sampledInducedGraph G z) (fun C => IsEmbeddedCycle C r) := by
  obtain ⟨N,hN⟩ := cycle_fractional_on_subset r hr (α/4) (by positivity)
  refine ⟨N,?_⟩
  intro V _ _ m hm G z hz
  apply hN V (retainedGraph G z.2) z.1.val (by simpa only [z.1.property] using hm)
  intro v hv
  have hh := (hz v hv).le
  rw [retainedNeighbourCount_eq] at hh
  simpa only [z.1.property] using hh

end Oberwolfach
