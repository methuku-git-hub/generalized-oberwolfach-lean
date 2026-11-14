module

public import Oberwolfach.MarkedPhysicalEdges
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

/-! Degrees of deleted auxiliary arcs are bounded by the degree of the
actual deleted physical graph. A marked incoming arc is charged at π v. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem deleted_pair_outdegree {I V:Type} [Fintype I] [Fintype V] [DecidableEq V]
    (a c:I→V) (hinj:Function.Injective (fun i=>({a i,c i}:Finset V))) (D:SimpleGraph V) (x:V):
    (∑ i,if D.Adj (a i) (c i)∧a i=x then (1:ℝ) else 0)≤D.degree x:=by
  have hh:(Finset.univ.filter (fun i=>D.Adj (a i) (c i)∧a i=x)).card≤(D.neighborFinset x).card:=by
    apply Finset.card_le_card_of_injOn c
    · intro i hi
      obtain ⟨_,hi,he⟩:=Finset.mem_filter.mp hi
      change c i∈D.neighborFinset x
      apply (D.mem_neighborFinset x (c i)).mpr
      exact he ▸ hi
    · intro i hi j hj hc
      obtain ⟨_,hi,he⟩:=Finset.mem_filter.mp hi
      obtain ⟨_,hj,hf⟩:=Finset.mem_filter.mp hj
      apply hinj
      change ({a i,c i}:Finset V)={a j,c j}
      rw [he,hf,hc]
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hh
  have hsum:(∑ i,if D.Adj (a i) (c i)∧a i=x then (1:ℝ) else 0)=
      ((Finset.univ.filter (fun i=>D.Adj (a i) (c i)∧a i=x)).card:ℝ):=by
    simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [hsum]
  exact_mod_cast hh

theorem deleted_pair_indegree {I V:Type} [Fintype I] [Fintype V] [DecidableEq V]
    (a c:I→V) (hinj:Function.Injective (fun i=>({a i,c i}:Finset V))) (D:SimpleGraph V) (x:V):
    (∑ i,if D.Adj (a i) (c i)∧c i=x then (1:ℝ) else 0)≤D.degree x:=by
  have hi:Function.Injective (fun i=>({c i,a i}:Finset V)):=by
    intro i j he
    apply hinj
    simpa only [Finset.pair_comm] using he
  simpa only [D.adj_comm] using deleted_pair_outdegree c a hi D x

theorem marked_physical_rim_deletion_degrees {V E K:Type} [Fintype V] [Fintype E] [Fintype K]
    [DecidableEq V] (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π)) (D:SimpleGraph V)
    (d:ℝ) (hD:∀ v,(D.degree v:ℝ)≤d):
    (∀ v,(∑ e,if D.Adj (tail e) (head e)∧tail e=v then (1:ℝ) else 0)≤d)∧
    (∀ v,(∑ e,if D.Adj (tail e) (head e)∧head e=v then (1:ℝ) else 0)≤d)∧
    (∀ v,(∑ e,if D.Adj (ktail e) (π (khead e))∧ktail e=v then (1:ℝ) else 0)≤d)∧
    (∀ v,(∑ e,if D.Adj (ktail e) (π (khead e))∧khead e=v then (1:ℝ) else 0)≤d):=by
  have hO:Function.Injective (fun e:E=>({tail e,head e}:Finset V)):=by
    intro e f he
    exact Sum.inl.inj (hp (show markedPhysicalEdge tail head ktail khead π (Sum.inl e)=
      markedPhysicalEdge tail head ktail khead π (Sum.inl f) from he))
  have hK:Function.Injective (fun e:K=>({ktail e,π (khead e)}:Finset V)):=by
    intro e f he
    exact Sum.inr.inj (hp (show markedPhysicalEdge tail head ktail khead π (Sum.inr e)=
      markedPhysicalEdge tail head ktail khead π (Sum.inr f) from he))
  refine ⟨fun v=>(deleted_pair_outdegree tail head hO D v).trans (hD v),
    fun v=>(deleted_pair_indegree tail head hO D v).trans (hD v),
    fun v=>(deleted_pair_outdegree ktail (fun e=>π (khead e)) hK D v).trans (hD v),?_⟩
  intro v
  simpa only [Equiv.apply_eq_iff_eq] using
    (deleted_pair_indegree ktail (fun e=>π (khead e)) hK D (π v)).trans (hD (π v))

end Oberwolfach
