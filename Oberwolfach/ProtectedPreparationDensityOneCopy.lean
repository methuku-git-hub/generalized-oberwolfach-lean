module

public import Oberwolfach.ProtectedFactorPreparation
public import Oberwolfach.FactorDecompositionSingleCopy

@[expose] public section
/-! At density one the sample and regular class are the host. A protected
preparation event therefore gives a copy of its repeated factor. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem protected_preparation_density_one_copy {n D:ℕ}
    (G F:SimpleGraph (Fin n)) (hD:0<D) (hEven:Even D)
    (hG:G.IsRegularOfDegree D) (hF:F.IsRegularOfDegree 2)
    (I:Finset (Fin n)) (ξ:ℝ) (hξ:0≤ξ) (B:ℕ)
    (hPrep:ProtectedFactorPreparation G G I ξ B (fun _:Fin (D/2)=>F)):
    ∃H:SimpleGraph (Fin n),H≤G ∧ H.IsRegularOfDegree 2 ∧ Nonempty (H ≃g F) :=by
  obtain ⟨A,hA,hAcap,hRobust⟩:=hPrep
  have hDhalf:2*(D/2)=D:=by have hdiv:=hEven.two_dvd;omega
  have hq:0<D/2:=by have hdiv:=hEven.two_dvd;omega
  have hreg:G.IsRegularOfDegree (2*(D/2)):=by simpa only [hDhalf] using hG
  have hDiff:∀x:Fin n,((Finset.univ.filter (fun y=>Xor (G.Adj x y) (G.Adj x y))).card:ℝ)≤ξ*n:=by
    intro x
    have hEmpty:(Finset.univ.filter (fun y=>Xor (G.Adj x y) (G.Adj x y)))=∅:=by
      ext y
      simp [Xor]
    rw [hEmpty]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity
  have hdec:=hRobust G le_rfl hreg hA (by intros; rfl) hDiff
  exact factor_decomposition_single_copy hq G F hF hdec
end Oberwolfach
