module

public import Oberwolfach.ClassCommonRetainedInputs
public import Oberwolfach.GoodPlacementEvents
public import Oberwolfach.CommonEvents

@[expose] public section
/-! A single global outcome satisfies every class event and the partition event
when their actual failure probabilities have total less than one. No
independence between the projected class events is assumed. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem class_common_event_union {I Ω C:Type} [Fintype I] [Fintype Ω] [Fintype C]
    {A:I→Type} [∀ i,Fintype (A i)]
    (global:FiniteLaw Ω) (colour:Ω→C) (colourLaw:FiniteLaw C)
    (view:∀ i,Ω→A i) (classLaw:∀ i,FiniteLaw (A i))
    (hcolour:global.map colour=colourLaw) (hview:∀ i,global.map (view i)=classLaw i)
    (Partition:C→Prop) (Good:∀ i,A i→Prop) (errPart:ℝ) (err:I→ℝ)
    (hpart:1-errPart≤colourLaw.probability Partition)
    (hgood:∀ i,1-err i≤(classLaw i).probability (Good i))
    (hbudget:errPart+∑ i,err i<1):
    ∃ ω,0<global.mass ω ∧ Partition (colour ω) ∧ ∀ i,Good i (view i ω):=by
  let P:=fun ω=>Partition (colour ω)
  let E:=fun i ω=>Good i (view i ω)
  have hp:1-errPart≤global.probability P:=by
    have hh:=finiteLaw_map_probability global colour Partition
    rw [hcolour] at hh
    exact hpart.trans_eq hh
  have hg (i:I):1-err i≤global.probability (E i):=by
    have hh:=finiteLaw_map_probability global (view i) (Good i)
    rw [hview i] at hh
    exact (hgood i).trans_eq hh
  let Bad:=fun ω=>∃ i,¬E i ω
  have hbad:global.probability Bad≤∑ i,err i:=by
    have hu:=finiteLaw_union_bound global (Finset.univ:Finset I) (fun i ω=>¬E i ω)
    calc
      _ ≤ ∑ i,global.probability (fun ω=>¬E i ω):=by simpa [Bad] using hu
      _ ≤ ∑ i,err i:=by
        apply Finset.sum_le_sum
        intro i _
        have hc:=finiteLaw_probability_compl global (E i)
        linarith [hg i]
  have hall:1-(∑ i,err i)≤global.probability (fun ω=>∀ i,E i ω):=by
    have hc:=finiteLaw_probability_compl global (fun ω=>∀ i,E i ω)
    have he:(fun ω=>¬∀ i,E i ω)=Bad:=by
      funext ω
      apply propext
      simp [Bad]
    rw [he] at hc
    linarith
  have hjoin:=finiteLaw_good_intersection global P (fun ω=>∀ i,E i ω) (∑ i,err i) hall
  have hpositive:0<global.probability (fun ω=>P ω ∧ ∀ i,E i ω):=by linarith
  unfold FiniteLaw.probability at hpositive
  have hnonneg:∀ ω∈(Finset.univ:Finset Ω),0≤(if P ω ∧ ∀ i,E i ω then global.mass ω else 0):=by
    intro ω _
    split_ifs
    · exact global.nonneg ω
    · norm_num
  have hpositive':0<∑ ω:Ω,if P ω ∧ ∀ i,E i ω then global.mass ω else 0:=by
    convert hpositive using 1
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h:P ω ∧ ∀ i,E i ω <;> simp [h]
  obtain ⟨ω,_,hω⟩:=(Finset.sum_pos_iff_of_nonneg hnonneg).mp hpositive'
  by_cases h:P ω ∧ ∀ i,E i ω
  · exact ⟨ω,by simpa [h] using hω,h.1,h.2⟩
  · simp [h] at hω
end Oberwolfach
