module

public import Oberwolfach.OrdinaryVertexTransfer
public import Oberwolfach.IndexedWheelLoads

@[expose] public section

/-! Labelled transfer configurations and their actual ordinary wheel weights.
All required rim edges, both sets of spokes, and forbidden edges are explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

structure OrdinaryTransferConfiguration {V U : Type*} {r : ℕ} (hr : 3≤r)
    (Q F : SimpleGraph V) (H : V → U → Prop) (v : V) (u u' : U) where
  labels : (Fin r × Fin r) ↪ V
  omitted : v∉Set.range labels
  rim_edges : ∀ j : TransferCycleIndex r,transferCycleGraph (by omega) labels v omitted j≤Q
  spokes : ∀ z∈insert v (Set.range labels),H z u ∧ H z u'
  independent : ∀ x∈insert v (Set.range labels),∀ y∈insert v (Set.range labels),¬F.Adj x y

instance {V U : Type*} [Fintype V] {r : ℕ} {hr : 3≤r}
    {Q F : SimpleGraph V} {H : V → U → Prop} {v : V} {u u' : U} :
    Fintype (OrdinaryTransferConfiguration hr Q F H v u u') :=
  Fintype.ofInjective (fun T => T.labels) (by
    intro T T' h
    cases T
    cases T'
    cases h
    rfl)

theorem transferCycleGraph_support_subset {V : Type*} {r : ℕ} (hr : 3≤r)
    (f : (Fin r × Fin r) ↪ V) (v : V) (hv : v∉Set.range f)
    (j : TransferCycleIndex r) :
    (transferCycleGraph (by omega) f v hv j).support⊆insert v (Set.range f) := by
  rcases j with ⟨⟩|⟨i,b⟩
  · rw [transferCycleGraph,cycle_map_support hr]
    rintro z ⟨i,rfl⟩
    exact Set.mem_insert_of_mem _ ⟨(i,⟨0,by omega⟩),rfl⟩
  · cases b
    · rw [transferCycleGraph,cycle_map_support hr]
      rintro z ⟨j,rfl⟩
      exact Set.mem_insert_of_mem _ ⟨(i,j),rfl⟩
    · rw [transferCycleGraph,cycle_map_support hr]
      rintro z ⟨j,rfl⟩
      change (if j=⟨0,by omega⟩ then v else f (i,j))∈insert v (Set.range f)
      split_ifs
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ ⟨(i,j),rfl⟩

def OrdinaryTransferConfiguration.wheel {V U : Type*} {r : ℕ} {hr : 3≤r}
    {Q F : SimpleGraph V} {H : V → U → Prop} {v : V} {u u' : U}
    (T : OrdinaryTransferConfiguration hr Q F H v u u') (b : Bool)
    (j : TransferCycleIndex r) : OrdinaryWheel Q F H r :=
  ⟨(⟨⟨transferCycleGraph (by omega) T.labels v T.omitted j,
      transferCycleGraph_isCycle hr T.labels v T.omitted j⟩,T.rim_edges j⟩,
      if b then u else u'),by
    constructor
    · intro z hz
      have hh := T.spokes z (transferCycleGraph_support_subset hr T.labels v T.omitted j hz)
      cases b
      · exact hh.2
      · exact hh.1
    · intro x hx y hy
      exact T.independent x (transferCycleGraph_support_subset hr T.labels v T.omitted j hx)
        y (transferCycleGraph_support_subset hr T.labels v T.omitted j hy)⟩

def OrdinaryTransferConfiguration.weight {V U : Type*} {r : ℕ} {hr : 3≤r}
    {Q F : SimpleGraph V} {H : V → U → Prop} {v : V} {u u' : U}
    (T : OrdinaryTransferConfiguration hr Q F H v u u') : OrdinaryWheel Q F H r → ℝ :=
  indexedWheelWeight (T.wheel true) transferCycleCoefficient-
    indexedWheelWeight (T.wheel false) transferCycleCoefficient

theorem OrdinaryTransferConfiguration.loads {V U : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U] {r : ℕ} {hr : 3≤r}
    {Q F : SimpleGraph V} {H : V → U → Prop} {v : V} {u u' : U}
    (T : OrdinaryTransferConfiguration hr Q F H v u u') :
    (∀ x y,ordinaryRimLoad T.weight x y=0) ∧
    (∀ z h,ordinarySpokeLoad T.weight z h=
      (if z=v then (1:ℝ) else 0)*((if h=u then 1 else 0)-(if h=u' then 1 else 0))) := by
  apply indexed_wheel_transfer_loads (T.wheel true) (T.wheel false) transferCycleCoefficient v u u'
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  intro z
  have hh := transfer_index_vertex_load hr T.labels v T.omitted z
  convert hh using 1
  · apply Finset.sum_congr rfl
    intro j _
    dsimp only [ordinaryWheelRim,OrdinaryTransferConfiguration.wheel]
    split_ifs <;> rfl
  · split_ifs <;> rfl

end Oberwolfach
