module

public import Oberwolfach.OrdinaryTransferCycles

@[expose] public section

/-! A signed weighting of actual cycle subgraphs whose vertex-load vector
is the unit vector at a specified root. Its constituent cycles are all explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem injective_range_indicator {I V : Type*} [Fintype I]
    (f : I ↪ V) (z : V) :
    (∑ i,if f i=z then (1:ℝ) else 0)=if z∈Set.range f then 1 else 0 := by
  classical
  by_cases hz : z∈Set.range f
  · obtain ⟨i,rfl⟩ := hz
    simp only [f.injective.eq_iff,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    simp
  · rw [if_neg hz]
    apply Finset.sum_eq_zero
    intro i _
    exact if_neg (fun h => hz ⟨i,h⟩)

abbrev TransferCycleIndex (r : ℕ) := Unit ⊕ (Fin r × Bool)

def transferCycleGraph {V : Type*} {r : ℕ} (hr : 0<r)
    (f : (Fin r × Fin r) ↪ V) (v : V) (hv : v∉Set.range f)
    (j : TransferCycleIndex r) : SimpleGraph V :=
  match j with
  | Sum.inl _ => (SimpleGraph.cycleGraph r).map (transferBaseEmbedding hr f)
  | Sum.inr (i,true) => (SimpleGraph.cycleGraph r).map (transferRootedEmbedding hr f v hv i)
  | Sum.inr (i,false) => (SimpleGraph.cycleGraph r).map (transferRowEmbedding f i)

def transferCycleCoefficient {r : ℕ} (j : TransferCycleIndex r) : ℝ :=
  match j with
  | Sum.inl _ => 1/r
  | Sum.inr (_,true) => 1/r
  | Sum.inr (_,false) => -(1/r)

def ordinaryVertexTransfer {V : Type*} {r : ℕ} (hr : 0<r)
    (f : (Fin r × Fin r) ↪ V) (v : V) (hv : v∉Set.range f) : SimpleGraph V → ℝ :=
  indexedFractionalWeight (transferCycleGraph hr f v hv) transferCycleCoefficient

theorem transferCycleGraph_isCycle {V : Type*} {r : ℕ} (hr : 3≤r)
    (f : (Fin r × Fin r) ↪ V) (v : V) (hv : v∉Set.range f)
    (j : TransferCycleIndex r) : IsEmbeddedCycle (transferCycleGraph (by omega) f v hv j) r := by
  rcases j with ⟨⟩|⟨i,b⟩
  · exact ⟨hr,transferBaseEmbedding (by omega) f,rfl⟩
  · cases b
    · exact ⟨hr,transferRowEmbedding f i,rfl⟩
    · exact ⟨hr,transferRootedEmbedding (by omega) f v hv i,rfl⟩

theorem transfer_index_vertex_load {V : Type*} {r : ℕ} (hr : 3≤r)
    (f : (Fin r × Fin r) ↪ V) (v : V) (hv : v∉Set.range f) (z : V) :
    (∑ j : TransferCycleIndex r,transferCycleCoefficient j*
      (if z∈(transferCycleGraph (by omega) f v hv j).support then (1:ℝ) else 0))=
      if z=v then 1 else 0 := by
  have hr' : (0:ℝ)<r := Nat.cast_pos.mpr (by omega)
  have hbase := injective_range_indicator (transferBaseEmbedding (by omega) f) z
  have hrow (i : Fin r) := transfer_rooted_range_difference (by omega) f v hv i z
  simp only [Fintype.sum_sum_type,Fintype.sum_unique,Fintype.sum_prod_type,Fintype.sum_bool,
    transferCycleCoefficient,transferCycleGraph,cycle_map_support hr]
  have hsum : (∑ i : Fin r, ((1/(r:ℝ))*(if z∈Set.range (transferRootedEmbedding (by omega) f v hv i) then 1 else 0)+
      (-(1/(r:ℝ)))*(if z∈Set.range (transferRowEmbedding f i) then 1 else 0)))=
      (1/(r:ℝ))*((r:ℝ)*(if z=v then 1 else 0)-
        (if z∈Set.range (transferBaseEmbedding (by omega) f) then 1 else 0)) := by
    calc
      _ = ∑ i : Fin r,(1/(r:ℝ))*((if z=v then 1 else 0)-(if z=f (i,⟨0,by omega⟩) then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        have hh := hrow i
        linarith [congrArg (fun x => (1/(r:ℝ))*x) hh]
      _ = _ := by
        rw [← Finset.mul_sum,Finset.sum_sub_distrib]
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        have hb : (∑ i : Fin r,if z=f (i,⟨0,by omega⟩) then (1:ℝ) else 0)=
            if z∈Set.range (transferBaseEmbedding (by omega) f) then 1 else 0 := by
          convert hbase using 1
          apply Finset.sum_congr rfl
          intro i _
          simp only [transferBaseEmbedding,Function.Embedding.coeFn_mk,eq_comm]
        rw [hb]
  rw [hsum]
  field_simp
  ring

theorem ordinaryVertexTransfer_vertex_load {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} (hr : 3≤r) (f : (Fin r × Fin r) ↪ V)
    (v : V) (hv : v∉Set.range f) (z : V) :
    (∑ C : SimpleGraph V,if z∈C.support then ordinaryVertexTransfer (by omega) f v hv C else 0)=
      if z=v then 1 else 0 := by
  have hh := finite_marginal_test transferCycleCoefficient (transferCycleGraph (by omega) f v hv)
    (ordinaryVertexTransfer (by omega) f v hv) (fun _ => rfl)
    (fun C : SimpleGraph V => if z∈C.support then (1:ℝ) else 0)
  have ht := transfer_index_vertex_load hr f v hv z
  calc
    _ = ∑ C : SimpleGraph V,ordinaryVertexTransfer (by omega) f v hv C*
        (if z∈C.support then (1:ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro C _
      split_ifs <;> simp
    _ = _ := hh.symm
    _ = _ := by
      convert ht using 1
      · apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> rfl
      · split_ifs <;> rfl

end Oberwolfach
