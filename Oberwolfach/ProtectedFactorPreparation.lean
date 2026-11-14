module

public import Oberwolfach.ProtectedPartitionIndexedFamilySameColour

@[expose] public section
/-! The graph-level preparation event appearing in the manuscript: a bounded
protected graph in the sample supports every permitted regular subgraph. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def ProtectedFactorPreparation {n m:ℕ} (P S₀:SimpleGraph (Fin n))
    (I:Finset (Fin n)) (ξ:ℝ) (B:ℕ) (F:Fin m→SimpleGraph (Fin n)):Prop :=
    ∃A:SimpleGraph (Fin n),A≤S₀ ∧ A.edgeFinset.card≤B ∧
      ∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*m)→A≤S→
        (∀x∈I,∀y∈I,S.Adj x y↔S₀.Adj x y)→
        (∀x,((Finset.univ.filter (fun y=>Xor (S.Adj x y) (S₀.Adj x y))).card:ℝ)≤ξ*n)→
        HasFactorDecomposition S F
end Oberwolfach
