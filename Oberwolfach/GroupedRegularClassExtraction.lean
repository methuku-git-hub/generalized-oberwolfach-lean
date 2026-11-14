module

public import Oberwolfach.ExpandedBinaryClassGraph
public import Oberwolfach.Neighbourhoods
public import Oberwolfach.Definitions

@[expose] public section
/-! Extract the actual regular class and the symmetric-difference edit bound
from the protected binary partition witness. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem changed_neighbourhoods_eq_xor
    {V:Type} [Fintype V] [DecidableEq V] (S₀ S:SimpleGraph V) (v:V):
    changed (S₀.neighborFinset v) (S.neighborFinset v)=
      Finset.univ.filter (fun w=>Xor (S.Adj v w) (S₀.Adj v w)):=by
  ext w
  simp only [changed,Finset.mem_union,Finset.mem_sdiff,SimpleGraph.mem_neighborFinset,
    Finset.mem_filter,Finset.mem_univ,true_and]
  unfold Xor
  tauto

theorem grouped_regular_class_extraction
    {n:ℕ} {U Γ Color:Type} [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
    (P Z A:SimpleGraph (Fin n)) (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Γ Color e)
    (m:Fin 2→ℕ) (H:Fin 2→SimpleGraph (Fin n)) (ξ:ℝ)
    (hpart:EdgePartition P H) (hreg:∀a,(H a).IsRegularOfDegree (2*m a))
    (hprotect:∀a x y,(Z⊔A).Adj x y→((H a).Adj x y↔
      (edgeColourGraph P (fun e=>(expandedBinaryClass (σ (Sum.inl e))).1) a).Adj x y))
    (hedit:∀a x,((Finset.univ.filter (fun y=>Xor ((H a).Adj x y)
      ((edgeColourGraph P (fun e=>(expandedBinaryClass (σ (Sum.inl e))).1) a).Adj x y))).card:ℝ)≤ξ*n):
    ∃S:SimpleGraph (Fin n),S≤P ∧ S.IsRegularOfDegree (2*m 0) ∧
      (∀x y,(Z⊔A).Adj x y→(S.Adj x y↔(longPhysicalStateGraph P σ {0,1,2,3,4}).Adj x y)) ∧
      (∀v,((changed ((longPhysicalStateGraph P σ {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n):=by
  refine ⟨H 0,?_,hreg 0,?_,?_⟩
  · intro x y h
    exact (hpart x y).1.mpr ⟨0,h⟩
  · intro x y h
    have hh:=hprotect 0 x y h
    rw [expanded_binary_class_graph P σ] at hh
    exact hh
  · intro v
    rw [changed_neighbourhoods_eq_xor]
    have hh:=hedit 0 v
    rw [expanded_binary_class_graph P σ] at hh
    exact hh
end Oberwolfach
