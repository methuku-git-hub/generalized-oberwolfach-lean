module

public import Oberwolfach.InitialDensityOneRegularHost
public import Oberwolfach.RepeatedFactorDensityOne
public import Oberwolfach.RegularCycleIsomorphism
public import Oberwolfach.FactorDecompositionSingleCopy

@[expose] public section
/-! At density one a selected regular class is the entire host, so its
factor decomposition supplies a copy of any repeatedly prescribed factor. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem selected_density_one_factor_host
    {n D q:ℕ} (P:SimpleGraph (Fin n)) (F:Fin q→SimpleGraph (Fin n))
    (hD:0<D) (hreg:P.IsRegularOfDegree D)
    (hone:initialIndexDensity (Fin q) D=1)
    (hSelected:∃S:SimpleGraph (Fin n),S≤P ∧ S.IsRegularOfDegree (2*Fintype.card (Fin q)) ∧ HasFactorDecomposition S F):
    HasFactorDecomposition P F :=by
  obtain ⟨S,hSP,hS,hdec⟩:=hSelected
  have hP:=initial_density_one_regular_host P D hD hreg hone
  have hEq:S=P:=regular_subgraph_eq hSP hP hS
  simpa only [hEq] using hdec

theorem selected_repeated_factor_single_copy
    {n D:ℕ} (P F:SimpleGraph (Fin n)) (hD:0<D) (hEven:Even D)
    (hreg:P.IsRegularOfDegree D) (hF:F.IsRegularOfDegree 2)
    (hSelected:∃S:SimpleGraph (Fin n),S≤P ∧ S.IsRegularOfDegree (2*Fintype.card (Fin (D/2))) ∧
      HasFactorDecomposition S (fun _:Fin (D/2)=>F)):
    ∃H:SimpleGraph (Fin n),H≤P ∧ H.IsRegularOfDegree 2 ∧ Nonempty (H ≃g F) :=by
  have hq:0<D/2:=by have hdiv:=hEven.two_dvd; omega
  have hdec:=selected_density_one_factor_host P (fun _:Fin (D/2)=>F) hD hreg (repeated_factor_density_one D hD hEven) hSelected
  exact factor_decomposition_single_copy hq P F hF hdec
end Oberwolfach
