module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Oberwolfach.FiniteHighEventsCommon

@[expose] public section
/-! Closed-neighbourhood sizes for graphs of maximum degree two. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {X:Type} [Fintype X] [DecidableEq X]

def prescribedClosedNeighbourhood (Q:SimpleGraph X) (v:X):Finset X:=
  insert v (Q.neighborFinset v)

def prescribedClosedNeighbourhoods (Q:SimpleGraph X) (S:Finset X):Finset X:=
  S.biUnion (prescribedClosedNeighbourhood Q)

theorem prescribed_closed_neighbourhood_card (Q:SimpleGraph X) (hdeg:∀x,Q.degree x≤2) (v:X):
    (prescribedClosedNeighbourhood Q v).card≤3 := by
  calc
    (prescribedClosedNeighbourhood Q v).card≤(Q.neighborFinset v).card+1:=Finset.card_insert_le _ _
    _=Q.degree v+1:=by rw [Q.card_neighborFinset_eq_degree]
    _≤3:=by have h:=hdeg v;omega

theorem prescribed_closed_neighbourhoods_card (Q:SimpleGraph X) (hdeg:∀x,Q.degree x≤2) (S:Finset X):
    (prescribedClosedNeighbourhoods Q S).card≤3*S.card := by
  calc
    (prescribedClosedNeighbourhoods Q S).card≤∑ v∈S,(prescribedClosedNeighbourhood Q v).card:=Finset.card_biUnion_le
    _≤∑ _v∈S,3:=by
      apply Finset.sum_le_sum
      intro v hv
      exact prescribed_closed_neighbourhood_card Q hdeg v
    _=3*S.card:=by simp [Nat.mul_comm]

theorem prescribed_edge_closed_neighbourhood_card (Q:SimpleGraph X) (hdeg:∀x,Q.degree x≤2)
    (u v:X) (huv:Q.Adj u v):
    (prescribedClosedNeighbourhood Q u∪prescribedClosedNeighbourhood Q v).card≤4 := by
  have hv:v∈Q.neighborFinset u:=(Q.mem_neighborFinset u v).mpr huv
  have hu:u∈Q.neighborFinset v:=(Q.mem_neighborFinset v u).mpr huv.symm
  have hnu:((Q.neighborFinset u).erase v).card≤1:=by
    have hd:=hdeg u
    have hc:=Finset.card_erase_of_mem hv
    rw [Q.card_neighborFinset_eq_degree] at hc
    omega
  have hnv:((Q.neighborFinset v).erase u).card≤1:=by
    have hd:=hdeg v
    have hc:=Finset.card_erase_of_mem hu
    rw [Q.card_neighborFinset_eq_degree] at hc
    omega
  let T:Finset X:={u,v}∪(Q.neighborFinset u).erase v∪(Q.neighborFinset v).erase u
  have hsub:prescribedClosedNeighbourhood Q u∪prescribedClosedNeighbourhood Q v⊆T:=by
    intro x hx
    simp only [prescribedClosedNeighbourhood,Finset.mem_union,Finset.mem_insert] at hx
    simp only [T,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_erase]
    rcases hx with (hx|hx)|(hx|hx)
    · exact Or.inl (Or.inl (Or.inl hx))
    · by_cases h:x=v
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr ⟨h,hx⟩)
    · exact Or.inl (Or.inl (Or.inr hx))
    · by_cases h:x=u
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inr ⟨h,hx⟩
  have ht:T.card≤4:=by
    have hpair:({u,v}:Finset X).card≤2:=by
      calc
        ({u,v}:Finset X).card≤({v}:Finset X).card+1:=Finset.card_insert_le _ _
        _=2:=by simp
    have hsum:=Finset.card_union_le ({u,v}:Finset X) ((Q.neighborFinset u).erase v)
    have hsum':=Finset.card_union_le ({u,v}∪(Q.neighborFinset u).erase v) ((Q.neighborFinset v).erase u)
    dsimp [T]
    omega
  exact (Finset.card_le_card hsub).trans ht
end Oberwolfach
