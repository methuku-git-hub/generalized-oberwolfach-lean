module

public import Oberwolfach.ResidualEndpointCapacity

@[expose] public section
/-! Both endpoints of the deleted paths are distinct and lie in the
prescribed set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V I:Type} [Fintype V] [DecidableEq V] [DecidableEq I]

theorem disjoint_walk_endpoints_card_le (F:SimpleGraph V) (s:Finset I)
    (u v:I→V) (P:∀ i,F.Walk (u i) (v i))
    (hne:∀i∈s,u i≠v i)
    (hP:(↑s:Set I).PairwiseDisjoint (fun i=>(P i).support.toFinset))
    (A:Finset V) (hAu:∀i∈s,u i∈A) (hAv:∀i∈s,v i∈A):2*s.card≤A.card := by
  let ends:I→Finset V:=fun i=>{u i,v i}
  have hends : (↑s:Set I).PairwiseDisjoint ends := by
    intro i hi j hj hij
    apply (hP hi hj hij).mono <;>
      intro x hx <;>
      simp only [ends,Finset.mem_insert,Finset.mem_singleton] at hx <;>
      rcases hx with rfl|rfl <;> simp
  have hsub:s.biUnion ends⊆A := by
    intro x hx
    obtain ⟨i,hi,hx⟩:=Finset.mem_biUnion.mp hx
    simp only [ends,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl
    · exact hAu i hi
    · exact hAv i hi
  have hcount:(s.biUnion ends).card=2*s.card := by
    rw [Finset.card_biUnion hends]
    have hh:∀ i∈s,(ends i).card=2 := by
      intro i hi
      simp [ends,hne i hi]
    calc
      _ = ∑ i∈s,(2:ℕ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hh i hi
      _ = _ := by simp [mul_comm]
  rw [←hcount]
  exact Finset.card_le_card hsub
end Oberwolfach
