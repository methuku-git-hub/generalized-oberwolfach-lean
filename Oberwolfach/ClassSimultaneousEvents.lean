module

public import Oberwolfach.ClassCommonEventUnion
public import Oberwolfach.ClassCommonFailureBudget
public import Oberwolfach.PartitionFailureBudget

@[expose] public section
/-! Choose one positive failure tolerance from the fixed upper bound on the
number of classes and obtain a common positive-mass outcome. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem class_simultaneous_events (K:ℕ):
    ∃ χ:ℝ,0<χ ∧ ∃ N:ℕ,∀ k n:ℕ,k≤K+1→N≤n→
    ∀ (Ω C:Type) [Fintype Ω] [Fintype C] (A:Fin k→Type) [∀ i,Fintype (A i)]
      (global:FiniteLaw Ω) (colour:Ω→C) (colourLaw:FiniteLaw C)
      (view:∀ i,Ω→A i) (classLaw:∀ i,FiniteLaw (A i))
      (hcolour:global.map colour=colourLaw) (hview:∀ i,global.map (view i)=classLaw i)
      (Partition:C→Prop) (Good:∀ i,A i→Prop),
      1-1/(n:ℝ)^10≤colourLaw.probability Partition→
      (∀ i,1-(100*χ+100/(n:ℝ))≤(classLaw i).probability (Good i))→
      ∃ ω,0<global.mass ω ∧ Partition (colour ω) ∧ ∀ i,Good i (view i ω):=by
  obtain ⟨χ,hχ,N,hN⟩:=class_common_failure_budget K
  refine ⟨χ,hχ,max N 2,?_⟩
  intro k n hk hn Ω C _ _ A _ global colour colourLaw view classLaw hcolour hview Partition Good hpart hgood
  have hnN:N≤n:=(le_max_left _ _).trans hn
  have hn2:2≤n:=(le_max_right _ _).trans hn
  have hbudget0:=hN k n hk hnN
  have hpart0:=partition_failure_at_most_half n hn2
  have hbudget:1/(n:ℝ)^10+(∑ _i:Fin k,(100*χ+100/(n:ℝ)))<1:=by linarith
  exact class_common_event_union global colour colourLaw view classLaw hcolour hview Partition Good
    (1/(n:ℝ)^10) (fun _=>100*χ+100/(n:ℝ)) hpart hgood hbudget
end Oberwolfach
