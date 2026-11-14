module

public import Oberwolfach.ProtectedPreparationDensityOneCopy
public import Oberwolfach.CoordinateLocalLemma

@[expose] public section
/-! Positive probability of density-one preparation yields the single copy
needed for the ordinary small-class branch. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem protected_preparation_density_one_probability_copy {n D:ℕ}
    (G F:SimpleGraph (Fin n)) (hD:0<D) (hEven:Even D)
    (hG:G.IsRegularOfDegree D) (hF:F.IsRegularOfDegree 2)
    (I:Finset (Fin n)) (ξ:ℝ) (hξ:0≤ξ) (B:ℕ)
    (hProb:0<(FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin 1 (by norm_num) (by norm_num))).probability
      (fun σ=>ProtectedFactorPreparation G (retainedGraph G σ) I ξ B (fun _:Fin (D/2)=>F))):
    ∃H:SimpleGraph (Fin n),H≤G ∧ H.IsRegularOfDegree 2 ∧ Nonempty (H ≃g F) :=by
  let μ:=FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin 1 (by norm_num) (by norm_num))
  obtain ⟨σ,hMass,hPrep⟩:=finiteLaw_positive_event_exists μ _ hProb
  have htrue:∀e,σ e=true:=by
    intro e
    by_contra h
    have he:σ e=false:=by cases hs:σ e <;> simp_all
    have hz:μ.mass σ=0:=by
      change (∏e, (FiniteLaw.retentionCoin 1 (by norm_num) (by norm_num)).mass (σ e))=0
      apply Finset.prod_eq_zero (Finset.mem_univ e)
      simp [FiniteLaw.retentionCoin,he]
    linarith
  have hGraph:retainedGraph G σ=G:=by
    ext x y
    simp [retainedGraph,htrue]
  rw [hGraph] at hPrep
  exact protected_preparation_density_one_copy G F hD hEven hG hF I ξ hξ B hPrep
end Oberwolfach
