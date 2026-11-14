module

public import Oberwolfach.FactorPrunedFamilyRemoval
public import Oberwolfach.FactorReassembleRemovedList

@[expose] public section
/-! Reinsert the sequentially removed small classes after decomposing the
remaining family on the residual host. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_pruned_removal_reassembly {n q:ℕ} (hn:0<n)
    (K:ℕ) (hK:0<K) (classify:Fin q→Option (Fin K))
    (D:ℕ) (δ α κL κS:ℝ) (hδ:0≤δ) (hα:0<α)
    (hL0:0≤κL) (hS0:0≤κS) (hL:κL≤α/1000) (hS:κS≤α/(1000*(K:ℝ)))
    (G:SimpleGraph (Fin n)) (hG:G.IsRegularOfDegree D) (hEven:Even D)
    (hdegree:(δ+α)*(n:ℝ)≤D) (F:Fin q→SimpleGraph (Fin n))
    (hF:∀ w,(F w).IsRegularOfDegree 2):
    let fibres:=fun j:Option (Fin K)=>Finset.univ.filter (fun w=>classify w=j)
    let small:=fun j:Option (Fin K)=>
      ((fibres j).card:ℝ)<(if j=none then κL*n else κS*n)
    let removed:=Finset.univ.filter (fun w=>small (classify w))
    let e:Fin (Fintype.card {i:Fin q // i∉removed})≃{i:Fin q // i∉removed}:=
      (Fintype.equivFin {i:Fin q // i∉removed}).symm;
    (∀P:SimpleGraph (Fin n),∀d:ℕ,P.IsRegularOfDegree d→Even d→
      (δ+α/2)*(n:ℝ)≤d→∀w∈removed,HasFactorDecomposition P (fun _:Fin (d/2)=>F w))→
    (∀R:SimpleGraph (Fin n),R.IsRegularOfDegree (D-2*removed.card)→R≤G→
      (δ+α/2)*(n:ℝ)≤((D-2*removed.card:ℕ):ℝ)→
      HasFactorDecomposition R (fun j=>F (e j).val))→
    HasFactorDecomposition G F :=by
  intro fibres small removed e hSmall hRemaining
  obtain ⟨R,pieces,hreg,hsub,hmargin,hRel,hEach,hPair,hcover⟩:=
    factor_pruned_family_removal hn K hK classify D δ α κL κS hδ hα hL0 hS0 hL hS G hG hEven hdegree F hF hSmall
  apply factor_reassemble_removed_list G R F removed e pieces hRel hPair
  · intro H hH x y hxy
    exact (hEach H hH).2 x y hxy
  · exact hcover
  · exact hRemaining R hreg hsub hmargin
end Oberwolfach
