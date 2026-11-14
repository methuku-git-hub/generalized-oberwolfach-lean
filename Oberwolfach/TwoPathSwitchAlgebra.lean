module

public import Oberwolfach.DisjointPairSwitches
public import Oberwolfach.UndirectedTwoPathPacking
public import Oberwolfach.ColourRestriction

@[expose] public section

/-! Actual undirected edges and exact degree changes for simultaneous
colour swaps along the selected paths. Middle vertices cancel algebraically. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def twoPathEdge {I V : Type*} (x y z : I → V) (p : I×Bool) : Sym2 V :=
  if p.2 then s(z p.1,y p.1) else s(x p.1,z p.1)

theorem twoPathEdge_mem {I V : Type*} [DecidableEq V] (x y z : I → V) (i : I) (b : Bool) :
    twoPathEdge x y z (i,b)∈twoPathEdges (x i) (y i) (z i) := by
  cases b <;> simp [twoPathEdge,twoPathEdges]

def twoPathEdgeEmbedding {I V : Type*} [DecidableEq V] (x y z : I → V)
    (hxy : ∀ i,x i≠y i)
    (hdisj : ∀ i j,i≠j → Disjoint (twoPathEdges (x i) (y i) (z i))
      (twoPathEdges (x j) (y j) (z j))) : (I×Bool)↪Sym2 V where
  toFun := twoPathEdge x y z
  inj' := by
    intro ⟨i,a⟩ ⟨j,b⟩ he
    have hij : i=j := by
      by_contra hij
      exact Finset.disjoint_left.mp (hdisj i j hij) (twoPathEdge_mem x y z i a)
        (he.symm ▸ twoPathEdge_mem x y z j b)
    subst j
    have hn : s(x i,z i)≠s(z i,y i) := by
      intro hh
      rcases Sym2.eq_iff.mp hh with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> exact hxy i (by aesop)
    cases a <;> cases b <;> simp only [twoPathEdge,Bool.false_eq_true,ite_false,ite_true] at he
    · rfl
    · exact False.elim (hn he)
    · exact False.elim (hn he.symm)
    · rfl

theorem edgeColourGraph_edges {V : Type*} [Fintype V] {k : ℕ}
    (G : SimpleGraph V) (σ : Sym2 V → Fin k) (a : Fin k) :
    (edgeColourGraph G σ a).edgeFinset=G.edgeFinset.filter (fun e => σ e=a) := by
  ext e
  induction e using Sym2.ind with
  | _ u v => simp [edgeColourGraph,SimpleGraph.mem_edgeFinset]

theorem edgeColourGraph_degree_edge_sum {V R : Type*} [Fintype V] [DecidableEq V]
    [CommRing R] {k : ℕ} (G : SimpleGraph V) (σ : Sym2 V → Fin k) (a : Fin k) (v : V) :
    ((edgeColourGraph G σ a).degree v:R)=
      ∑ e : Sym2 V,(if e∈G.edgeFinset ∧ v∈e then (1:R) else 0)*(if σ e=a then 1 else 0) := by
  rw [← SimpleGraph.card_incidenceFinset_eq_degree,
    SimpleGraph.incidenceFinset_eq_filter,edgeColourGraph_edges,Finset.filter_filter,
    Finset.card_filter,Nat.cast_sum]
  have hf : (∑ e : Sym2 V,(if e∈G.edgeFinset ∧ v∈e then (1:R) else 0)*(if σ e=a then 1 else 0))=
      ∑ e∈G.edgeFinset,(if v∈e then (1:R) else 0)*(if σ e=a then 1 else 0) := by
    have hi (e : Sym2 V) : (if e∈G.edgeFinset ∧ v∈e then (1:R) else 0)*(if σ e=a then 1 else 0)=
        if e∈G.edgeFinset then (if v∈e then (1:R) else 0)*(if σ e=a then 1 else 0) else 0 := by
      by_cases he : e∈G.edgeFinset <;> simp [he]
    simp only [hi]
    rw [← Finset.sum_filter]
    have he : Finset.univ.filter (fun e => e∈G.edgeFinset)=G.edgeFinset := by ext e;simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    rw [he]
  rw [hf]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> simp_all

theorem edgeColourGraph_card_edge_sum {V R : Type*} [Fintype V] [DecidableEq V]
    [CommRing R] {k : ℕ} (G : SimpleGraph V) (σ : Sym2 V → Fin k) (a : Fin k) :
    ((edgeColourGraph G σ a).edgeFinset.card:R)=
      ∑ e : Sym2 V,(if e∈G.edgeFinset then (1:R) else 0)*(if σ e=a then 1 else 0) := by
  rw [edgeColourGraph_edges,Finset.card_filter,Nat.cast_sum]
  simp only [ite_mul,one_mul,zero_mul]
  rw [← Finset.sum_filter]
  have he : Finset.univ.filter (fun e => e∈G.edgeFinset)=G.edgeFinset := by ext e;simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  rw [he]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem edge_incidence_difference {V R : Type*} [DecidableEq V] [CommRing R]
    (x y z v : V) (hxz : x≠z) (hyz : y≠z) :
    (if v∈s(x,z) then (1:R) else 0)-(if v∈s(z,y) then 1 else 0)=
      (if x=v then 1 else 0)-(if y=v then 1 else 0) := by
  by_cases hx : x=v <;> by_cases hy : y=v <;> by_cases hz : z=v <;>
    simp_all [Sym2.mem_iff,eq_comm]

theorem twoPath_switch_degree_change {I V R : Type*} [Fintype I]
    [Fintype V] [DecidableEq V] [CommRing R] {k : ℕ}
    (G : SimpleGraph V) (σ : Sym2 V → Fin k) (x y z : I → V)
    (hxy : ∀ i,x i≠y i)
    (hdisj : ∀ i j,i≠j → Disjoint (twoPathEdges (x i) (y i) (z i))
      (twoPathEdges (x j) (y j) (z j)))
    (hxz : ∀ i,G.Adj (x i) (z i)) (hyz : ∀ i,G.Adj (z i) (y i))
    (a : Fin k) (v : V) :
    let ι := twoPathEdgeEmbedding x y z hxy hdisj
    ((edgeColourGraph G (σ ∘ pairSwitchPermutation ι) a).degree v:R)-
      ((edgeColourGraph G σ a).degree v:R)=
      ∑ i,((if x i=v then (1:R) else 0)-(if y i=v then 1 else 0))*
        ((if σ s(z i,y i)=a then 1 else 0)-(if σ s(x i,z i)=a then 1 else 0)) := by
  intro ι
  rw [edgeColourGraph_degree_edge_sum,edgeColourGraph_degree_edge_sum]
  have hh := pair_switch_weighted_difference ι σ
    (fun e => if e∈G.edgeFinset ∧ v∈e then (1:R) else 0) (fun b => if b=a then (1:R) else 0)
  change (∑ e,(if e∈G.edgeFinset ∧ v∈e then (1:R) else 0)*(if σ (pairSwitchPermutation ι e)=a then 1 else 0))-
    (∑ e,(if e∈G.edgeFinset ∧ v∈e then (1:R) else 0)*(if σ e=a then 1 else 0))=_
  rw [hh]
  apply Finset.sum_congr rfl
  intro i _
  have he1 : s(x i,z i)∈G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr (hxz i)
  have he2 : s(z i,y i)∈G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr (hyz i)
  have hi0 : ι (i,false)=s(x i,z i) := rfl
  have hi1 : ι (i,true)=s(z i,y i) := rfl
  simp only [hi0,hi1,he1,he2,true_and]
  rw [edge_incidence_difference (x i) (y i) (z i) v (hxz i).ne (hyz i).symm.ne]

theorem twoPath_switch_preserves_card {I V : Type*} [Fintype I]
    [Fintype V] [DecidableEq V] {k : ℕ}
    (G : SimpleGraph V) (σ : Sym2 V → Fin k) (x y z : I → V)
    (hxy : ∀ i,x i≠y i)
    (hdisj : ∀ i j,i≠j → Disjoint (twoPathEdges (x i) (y i) (z i))
      (twoPathEdges (x j) (y j) (z j)))
    (hxz : ∀ i,G.Adj (x i) (z i)) (hyz : ∀ i,G.Adj (z i) (y i)) (a : Fin k) :
    let ι := twoPathEdgeEmbedding x y z hxy hdisj
    (edgeColourGraph G (σ ∘ pairSwitchPermutation ι) a).edgeFinset.card=
      (edgeColourGraph G σ a).edgeFinset.card := by
  intro ι
  have he : ((edgeColourGraph G (σ ∘ pairSwitchPermutation ι) a).edgeFinset.card:ℤ)=
      ((edgeColourGraph G σ a).edgeFinset.card:ℤ) := by
    rw [edgeColourGraph_card_edge_sum,edgeColourGraph_card_edge_sum]
    apply pair_switch_preserves_weighted_sum ι σ _ (fun b => if b=a then (1:ℤ) else 0)
    intro i
    have he1 : s(x i,z i)∈G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr (hxz i)
    have he2 : s(z i,y i)∈G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr (hyz i)
    have hi0 : ι (i,false)=s(x i,z i) := rfl
    have hi1 : ι (i,true)=s(z i,y i) := rfl
    simp only [hi0,hi1,he1,he2,ite_true]
  exact_mod_cast he

end Oberwolfach
