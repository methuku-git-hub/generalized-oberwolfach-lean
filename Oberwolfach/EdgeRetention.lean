module

public import Oberwolfach.ColourDegrees
public import Oberwolfach.ConditionalRealization

@[expose] public section

/-! Independent retention of physical undirected edges with supplied,
possibly unequal probabilities. No edge is represented twice. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def FiniteLaw.retentionCoin (p : ℝ) (hp : 0≤p) (hp1 : p≤1) : FiniteLaw Bool where
  mass b := if b then p else 1-p
  nonneg b := by cases b <;> simp <;> linarith
  total := by simp [Fintype.sum_bool]

def retainedGraph {V : Type*} (G : SimpleGraph V) (σ : Sym2 V → Bool) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ σ s(u,v)=true
  symm := ⟨by intro u v h;simpa only [Sym2.eq_swap] using (show G.Adj v u ∧ σ s(u,v)=true from ⟨h.1.symm,h.2⟩)⟩
  loopless := ⟨by intro v h;exact G.ne_of_adj h.1 rfl⟩

theorem retainedGraph_le {V : Type*} (G : SimpleGraph V) (σ : Sym2 V → Bool) :
    retainedGraph G σ≤G := fun _ _ h => h.1

def retainedNeighbourCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (σ : Sym2 V → Bool) (v : V) : ℕ :=
  ((G.neighborFinset v∩S).filter (fun x => σ s(v,x)=true)).card

theorem retainedNeighbourCount_patterns {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (σ : Sym2 V → Bool) (v : V) :
    (retainedNeighbourCount G S σ v:ℝ)=
      ∑ x∈G.neighborFinset v∩S,patternValue {s(v,x)} (fun _ => true) σ := by
  simp only [retainedNeighbourCount,patternValue,Finset.prod_singleton,
    Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> rfl

theorem retainedNeighbourCount_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (σ : Sym2 V → Bool) (v : V) :
    retainedNeighbourCount G S σ v=((retainedGraph G σ).neighborFinset v∩S).card := by
  unfold retainedNeighbourCount
  congr 1
  ext x
  simp [retainedGraph,and_assoc,and_comm,and_left_comm]

theorem retained_neighbour_count_tail {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (μ : Sym2 V → FiniteLaw Bool) (v : V)
    (t : ℝ) (ht : 0≤t) :
    (FiniteLaw.pi μ).probability (fun σ =>
      t≤|(retainedNeighbourCount G S σ v:ℝ)-
        ∑ x∈G.neighborFinset v∩S,(μ s(v,x)).mass true|)≤
      2*Real.exp (-2*t^2/S.card) := by
  have hh := finiteLaw_singleton_patterns_tail_at_scale μ (G.neighborFinset v∩S)
    (fun x => s(v,x)) (fun _ _ => true) (fun _ _ _ _ h => incidentPair_injective v h)
    (n:=(S.card:ℝ)) (by exact_mod_cast Finset.card_le_card (Finset.inter_subset_right (s₁:=G.neighborFinset v) (s₂:=S))) ht
  simpa only [← retainedNeighbourCount_patterns] using hh

theorem retained_graph_edge_probability {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (μ : Sym2 V → FiniteLaw Bool) (u v : V) :
    (FiniteLaw.pi μ).probability (fun σ => (retainedGraph G σ).Adj u v)=
      if G.Adj u v then (μ s(u,v)).mass true else 0 := by
  by_cases hG : G.Adj u v
  · simp only [retainedGraph,hG,true_and,ite_true]
    exact finiteLaw_pi_coordinate_probability μ s(u,v) true
  · simp [retainedGraph,hG,FiniteLaw.probability]

end Oberwolfach
