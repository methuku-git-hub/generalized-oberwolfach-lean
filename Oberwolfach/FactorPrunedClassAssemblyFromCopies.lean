module

public import Oberwolfach.FactorPrunedRemovalReassemblyFromCopies
public import Oberwolfach.FactorDecompositionFromIndexedClasses

@[expose] public section
/-! Combine exact small-class reinsertion with decompositions of a protected
partition of the retained family, keeping all original factor indices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_pruned_class_assembly_from_copies {n q:ℕ} (hn:0<n)
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
      (δ+α/2)*(n:ℝ)≤d→∀w∈removed,∃ H:SimpleGraph (Fin n),H≤P ∧ H.IsRegularOfDegree 2 ∧ Nonempty (H ≃g F w))→
    (∀R:SimpleGraph (Fin n),R.IsRegularOfDegree (D-2*removed.card)→R≤G→
      (δ+α/2)*(n:ℝ)≤((D-2*removed.card:ℕ):ℝ)→
      ∃classes:Option (Fin K)→SimpleGraph (Fin n),
        (∀x y,(R.Adj x y↔∃j,(classes j).Adj x y) ∧
          ∀j k,(classes j).Adj x y→(classes k).Adj x y→j=k) ∧
        (∀j,
          let eqv:=Fintype.equivFin {i:Fin (Fintype.card {i:Fin q // i∉removed}) // classify (e i).val=j};
          HasFactorDecomposition (classes j) (fun k=>F (e (eqv.symm k).val).val)))→
    HasFactorDecomposition G F :=by
  intro fibres small removed e hSmall hClasses
  apply factor_pruned_removal_reassembly_from_copies hn K hK classify D δ α κL κS hδ hα hL0 hS0 hL hS G hG hEven hdegree F hF hSmall
  intro R hreg hsub hmargin
  obtain ⟨classes,hpart,hlocal⟩:=hClasses R hreg hsub hmargin
  exact factor_decomposition_from_indexed_classes R (fun i=>F (e i).val) classes (fun i=>classify (e i).val) hpart hlocal
end Oberwolfach
