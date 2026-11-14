module

public import Oberwolfach.MarkedPreparationReferenceIndices
public import Oberwolfach.SuccessorWeightsTheorem

@[expose] public section
/-! The marked weight choice meets the density inequality required by the
fixed-vortex reference theorem with the same cycle length. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_preparation_reference_margin (m:ℕ) (hm:6≤m) (heven:Even (m+1)) (α:ℝ)
    (hmargin:((m+1:ℕ):ℝ)/(2*((m+1:ℕ):ℝ)-2)+α/4≤1/2+α/2):
    ∃ r k₀:ℕ,2≤r ∧ r+4=m ∧ r+4+1=(k₀+2)*2 ∧
      successorCycleRatio k₀+α/4≤1/2+α/2:=by
  obtain ⟨r,k₀,hr,hmr,hlen⟩:=marked_preparation_reference_indices m hm heven
  refine ⟨r,k₀,hr,hmr,hlen,?_⟩
  rw [successorCycleRatio_standard]
  have hc:(m+1:ℕ)=(k₀+2)*2:=by omega
  simpa only [hc] using hmargin
end Oberwolfach
