module

public import Oberwolfach.OrdinaryCyclePairCount
public import Oberwolfach.OrdinaryCycleIncidence
public import Oberwolfach.CycleIndependentSampling
public import Oberwolfach.UniformWeightedHypergraphMatching

@[expose] public section
/-! The edges of the auxiliary hypergraph are the retained cycle identifiers;
its vertices are the vertices of the underlying graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

abbrev RetainedOrdinaryCycle {V:Type} (G:SimpleGraph V) (r:ℕ)
    (σ:OrdinaryCycle G r→Bool):= {C:OrdinaryCycle G r // σ C=true}

def retainedOrdinaryCycleVertices {V:Type} [Fintype V] [DecidableEq V]
    {G:SimpleGraph V} {r:ℕ} {σ:OrdinaryCycle G r→Bool}
    (C:RetainedOrdinaryCycle G r σ):Finset V := C.val.val.val.support.toFinset

theorem retained_ordinary_cycle_vertices_card {V:Type} [Fintype V] [DecidableEq V]
    {G:SimpleGraph V} {r:ℕ} {σ:OrdinaryCycle G r→Bool}
    (C:RetainedOrdinaryCycle G r σ):(retainedOrdinaryCycleVertices C).card=r:=by
  exact C.val.val.property.support_card

theorem retained_ordinary_cycle_degree {V:Type} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) (r:ℕ) [DecidableEq (OrdinaryCycle G r)]
    (σ:OrdinaryCycle G r→Bool) (v:V):
    (Fintype.card (HypergraphEdgesAt (retainedOrdinaryCycleVertices (G:=G) (r:=r) (σ:=σ)) v):ℝ)=
      independentCycleCount (fun C=>v∈C.val.val.support) σ := by
  let f : HypergraphEdgesAt (retainedOrdinaryCycleVertices (G:=G) (r:=r) (σ:=σ)) v ≃
      {C:OrdinaryCycle G r // σ C=true ∧ v∈C.val.val.support} := {
    toFun := fun e =>⟨e.val.val,⟨e.val.property,by simpa [retainedOrdinaryCycleVertices] using e.property⟩⟩
    invFun := fun C =>⟨⟨C.val,C.property.1⟩,by simpa [retainedOrdinaryCycleVertices] using C.property.2⟩
    left_inv := fun e => by cases e with | mk e h => cases e; rfl
    right_inv := fun C => by cases C; rfl }
  rw [Fintype.card_congr f]
  simp only [Fintype.card_subtype,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
    independentCycleCount]
  apply Finset.sum_congr rfl
  intro C _
  by_cases h1:σ C=true <;> by_cases h2:v∈C.val.val.support <;> simp [h1,h2]

theorem retained_ordinary_cycle_codegree {V:Type} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) (r:ℕ) [DecidableEq (OrdinaryCycle G r)]
    (σ:OrdinaryCycle G r→Bool) (u v:V):
    ((Finset.univ.filter (fun C:RetainedOrdinaryCycle G r σ=>
        u∈retainedOrdinaryCycleVertices C ∧ v∈retainedOrdinaryCycleVertices C)).card:ℝ)=
      independentCycleCount (fun C=>u∈C.val.val.support ∧ v∈C.val.val.support) σ := by
  let f : {C:RetainedOrdinaryCycle G r σ // u∈retainedOrdinaryCycleVertices C ∧
      v∈retainedOrdinaryCycleVertices C} ≃
      {C:OrdinaryCycle G r // σ C=true ∧ u∈C.val.val.support ∧ v∈C.val.val.support} := {
    toFun := fun C => ⟨C.val.val,⟨C.val.property,by simpa [retainedOrdinaryCycleVertices] using C.property⟩⟩
    invFun := fun C => ⟨⟨C.val,C.property.1⟩,by simpa [retainedOrdinaryCycleVertices] using C.property.2⟩
    left_inv := fun C => by cases C with | mk C h => cases C; rfl
    right_inv := fun C => by cases C; rfl }
  rw [←Fintype.card_subtype, Fintype.card_congr f]
  simp only [Fintype.card_subtype,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
    independentCycleCount]
  apply Finset.sum_congr rfl
  intro C _
  by_cases h1:σ C=true <;> by_cases h2:u∈C.val.val.support ∧ v∈C.val.val.support <;> simp [h1,h2]
end Oberwolfach
