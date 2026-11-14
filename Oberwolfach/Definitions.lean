module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/-! Exact finite-graph definitions for the main theorem.
`MainTheorem` and `FixedSetTheorem` are proposition definitions. Their proofs
are supplied in `Oberwolfach.MainTheoremFromProtectedPreparation`. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
open SimpleGraph

/-- A spanning family partitions edges exactly once. The vertices are shared. -/
def EdgePartition {n q : ℕ} (G : SimpleGraph (Fin n))
    (pieces : Fin q → SimpleGraph (Fin n)) : Prop :=
  ∀ u v, (G.Adj u v ↔ ∃ i, (pieces i).Adj u v) ∧
    ∀ i j, (pieces i).Adj u v → (pieces j).Adj u v → i = j

/-- Decomposition into the prescribed list, with actual graph isomorphisms. -/
def HasFactorDecomposition {n q : ℕ} (G : SimpleGraph (Fin n))
    (F : Fin q → SimpleGraph (Fin n)) : Prop :=
  ∃ pieces : Fin q → SimpleGraph (Fin n),
    EdgePartition G pieces ∧ ∀ i, Nonempty (pieces i ≃g F i)

/-- One cycle of length r embedded in the ambient n-vertex set; other vertices
are isolated. The two possible cyclic directions define undirected adjacency. -/
def IsCycleCopy {n : ℕ} (H : SimpleGraph (Fin n)) (r : ℕ) : Prop :=
  3 ≤ r ∧ ∃ f : Fin r ↪ Fin n, ∀ u v,
    H.Adj u v ↔ ∃ i j : Fin r, f i = u ∧ f j = v ∧
      ((i.val + 1) % r = j.val ∨ (j.val + 1) % r = i.val)

/-- Ordinary decompositions use small cycles, not spanning cycle factors. -/
def HasCycleDecomposition {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) : Prop :=
  ∃ q : ℕ, ∃ pieces : Fin q → SimpleGraph (Fin n),
    EdgePartition G pieces ∧ ∀ i, IsCycleCopy (pieces i) r

def CycleDivisible {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) : Prop := by
  classical
  exact (∀ v, Even (G.degree v)) ∧ r ∣ G.edgeFinset.card

/-- The infimum in the manuscript's definition of the ordinary threshold. -/
def AdmissibleCycleBound (r : ℕ) (d : ℝ) : Prop := by
  classical
  exact d ∈ Set.Icc (0 : ℝ) 1 ∧ ∃ N : ℕ, ∀ n ≥ N,
    ∀ G : SimpleGraph (Fin n), CycleDivisible G r →
      (∀ v, d * (n : ℝ) ≤ (G.degree v : ℝ)) → HasCycleDecomposition G r

noncomputable def cycleThreshold (r : ℕ) : ℝ := sInf {d | AdmissibleCycleBound r d}
noncomputable def allowedThreshold (S : Set ℕ) : ℝ := sSup (cycleThreshold '' S)

def AllowedCycleLengths {n : ℕ} (F : SimpleGraph (Fin n)) (S : Set ℕ) : Prop :=
  ∀ v : Fin n, Nat.card {w : Fin n // F.Reachable v w} ∈ S

/-- All inputs of Theorem 1.1 at a specified degree margin. -/
def DecompositionAt (S : Set ℕ) (α : ℝ) (n : ℕ) : Prop := by
  classical
  exact ∀ D : ℕ, Even D → (allowedThreshold S + α) * (n : ℝ) ≤ (D : ℝ) →
    ∀ F : Fin (D / 2) → SimpleGraph (Fin n),
      (∀ i, (F i).IsRegularOfDegree 2 ∧ AllowedCycleLengths (F i) S) →
      ∀ G : SimpleGraph (Fin n), G.IsRegularOfDegree D → HasFactorDecomposition G F

/-- Main target. In particular N is selected before S. -/
def MainTheorem : Prop :=
  ∀ α : ℝ, 0 < α → ∃ N : ℕ, ∀ S : Set ℕ,
    S.Nonempty → (∀ r ∈ S, 3 ≤ r) → ∀ n ≥ N, DecompositionAt S α n

/-- Fixed-set intermediate target. -/
def FixedSetTheorem : Prop :=
  ∀ S : Set ℕ, S.Nonempty → (∀ r ∈ S, 3 ≤ r) →
    ∀ α : ℝ, 0 < α → ∃ N : ℕ, ∀ n ≥ N, DecompositionAt S α n

end Oberwolfach
