module

public import Oberwolfach.BinaryClassMultiplicity
public import Oberwolfach.LongClassProtectedCorrectionAndDeletion

@[expose] public section
/-! The binary class selected from the pruning construction has the correct
multiplicity, and the original regular host gives the correction degree data. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem pruned_class_correction_inputs {n:ℕ} {U:Type} [Fintype U]
    (P:SimpleGraph (Fin n)) (D B:ℕ) (α ρ₀:ℝ)
    (hregular:P.IsRegularOfDegree D)
    (hD:(1/2+α)*(n:ℝ)≤D)
    (hB:(B:ℝ)≤(α*(ρ₀/200)^2/16)*n):
    binaryClassMultiplicity D (Fintype.card U) 0=Fintype.card U ∧
    (∀v,(P.degree v:ℝ)=D) ∧
    (∀v,(1/2+α)*(n:ℝ)≤P.degree v) ∧
    (B:ℝ)≤(α*(ρ₀/200)^2/16)*n ∧
    ∀A:SimpleGraph (Fin n),(∀v,A.degree v≤B)→
      ∀v,(((⊥:SimpleGraph (Fin n))⊔A).degree v:ℝ)≤B:=by
  refine ⟨rfl,?_,?_,hB,?_⟩
  · intro v; exact_mod_cast hregular.degree_eq v
  · intro v; simpa only [hregular.degree_eq v] using hD
  · intro A hA v
    have hA':(A.degree v:ℝ)≤B:=by exact_mod_cast hA v
    convert hA' using 1
    congr 1
    simp only [← SimpleGraph.ncard_neighborSet,bot_sup_eq]
end Oberwolfach
