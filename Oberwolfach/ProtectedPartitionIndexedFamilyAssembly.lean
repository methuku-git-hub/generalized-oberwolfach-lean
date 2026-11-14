module

public import Oberwolfach.ProtectedPartitionReadyClassAssembly
public import Oberwolfach.FactorDecompositionFromIndexedClasses

@[expose] public section
/-! Reassemble the prescribed indexed family after the protected partition;
no permutation of factor types or new host assumption is introduced. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem protected_partition_ready_indexed_family {n q k:ℕ}
    (G:SimpleGraph (Fin n)) (F:Fin q→SimpleGraph (Fin n)) (colour:Fin q→Fin k)
    (c:Sym2 (Fin n)→Fin k) (I:Fin k→Finset (Fin n)) (ξ:ℝ) (B:ℕ) (Ba:Fin k→ℕ)
    (hB:∑a,Ba a≤B):
    let m:Fin k→ℕ:=fun a=>Fintype.card {i:Fin q // colour i=a}
    let Fc:∀a,Fin (m a)→SimpleGraph (Fin n):=fun a j=>F ((Fintype.equivFin {i:Fin q // colour i=a}).symm j).val;
    (∀a,∃A:SimpleGraph (Fin n),A≤edgeColourGraph G c a ∧ A.edgeFinset.card≤Ba a ∧
      ∀H:SimpleGraph (Fin n),H≤G→H.IsRegularOfDegree (2*m a)→A≤H→
        (∀x∈I a,∀y∈I a,H.Adj x y↔(edgeColourGraph G c a).Adj x y)→
        (∀x,((Finset.univ.filter (fun y=>Xor (H.Adj x y) ((edgeColourGraph G c a).Adj x y))).card:ℝ)≤ξ*n)→
        HasFactorDecomposition H (Fc a))→
    (∀A:Fin k→SimpleGraph (Fin n),
      (∀a,A a≤edgeColourGraph G c a)→(∑a,(A a).edgeFinset.card)≤B→
      ∃H:Fin k→SimpleGraph (Fin n),
        EdgePartition G H ∧ (∀a,(H a).IsRegularOfDegree (2*m a)) ∧
        (∀a,A a≤H a) ∧
        (∀a b x,x∈I b→∀y,y∈I b→((H a).Adj x y↔(edgeColourGraph G c a).Adj x y)) ∧
        (∀a x,((Finset.univ.filter (fun y=>Xor ((H a).Adj x y) ((edgeColourGraph G c a).Adj x y))).card:ℝ)≤ξ*n))→
    HasFactorDecomposition G F :=by
  intro m Fc hReady hPartition
  obtain ⟨H,hpart,hdec⟩:=protected_partition_ready_class_assembly G c m Fc I ξ B Ba hB hReady hPartition
  exact factor_decomposition_from_indexed_classes G F H colour hpart hdec
end Oberwolfach
