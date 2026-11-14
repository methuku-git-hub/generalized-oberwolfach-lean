module

public import Oberwolfach.LongFixedPartitionDensityObstruction
public import Oberwolfach.ExpandedSamplePhysicalClassLaw

@[expose] public section
/-! An exact regular completion which agrees on a protected set cannot hide
more missing protected edges at a vertex than its total degree deficit. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_regular_completion_protected_deficit
    {V:Type} [Fintype V] [DecidableEq V] (P R S:SimpleGraph V)
    (D c:ℕ) (hP:P.IsRegularOfDegree D) (hS:S.IsRegularOfDegree (D-c))
    (hc:c≤D) (hsub:S≤P) (X:Finset V) (v:V) (hv:v∈X)
    (hagree:∀x∈X,∀y∈X,(S.Adj x y↔R.Adj x y)):
    ((P.neighborFinset v).filter (fun y=>y∈X ∧ ¬R.Adj v y)).card≤c :=by
  have hN:S.neighborFinset v⊆P.neighborFinset v:=by
    intro y hy
    exact (SimpleGraph.mem_neighborFinset _ _ _).mpr (hsub ((SimpleGraph.mem_neighborFinset _ _ _).mp hy))
  have hmissing:(P.neighborFinset v).filter (fun y=>y∈X ∧ ¬R.Adj v y)⊆
      P.neighborFinset v\S.neighborFinset v:=by
    intro y hy
    simp only [Finset.mem_filter,Finset.mem_sdiff,SimpleGraph.mem_neighborFinset] at hy ⊢
    exact ⟨hy.1,fun h=>hy.2.2 ((hagree v hv y hy.2.1).mp h)⟩
  have hcard:=Finset.card_le_card hmissing
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hN] at hcard
  simp only [SimpleGraph.card_neighborFinset_eq_degree,hP v,hS v] at hcard
  omega
end Oberwolfach
