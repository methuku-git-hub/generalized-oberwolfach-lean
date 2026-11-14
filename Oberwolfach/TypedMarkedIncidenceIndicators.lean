module

public import Oberwolfach.TypedMarkedSurvival
public import Oberwolfach.MarkedPhysicalLoads

@[expose] public section

/-! Exact typed incidence indicators on the potential wheel universe.
Only injectivity of each directed endpoint map is needed; its physical
images and its two spoke relations need not be disjoint. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ HK:V→U→Prop}

theorem markedCycleIncidence_canonical_indicator
    (hE:Function.Injective (fun e:E=>(tail e,head e)))
    (hK:Function.Injective (fun e:K=>(ktail e,khead e)))
    (C:MarkedCycleTuple tail head ktail khead m π b) (e:E⊕K):
    markedCycleIncidence tail head ktail khead m C.val e=
      if CanonicalMarkedArcMem C e then 1 else 0:=by
  rw [markedCycleIncidence_occurrences hE hK]
  have hh:=injective_occurrence_sum (markedCycleTypedEdge tail head ktail khead m π b C)
    (markedCycleTypedEdge_injective tail head ktail khead m π b C) e
  have hm : e ∈ Finset.univ.image (markedCycleTypedEdge tail head ktail khead m π b C) ↔
      CanonicalMarkedArcMem C e := by
    simp only [Finset.mem_image,Finset.mem_univ,true_and,CanonicalMarkedArcMem]
  by_cases he : CanonicalMarkedArcMem C e
  · simpa only [if_pos he,if_pos (hm.mpr he)] using hh
  · simpa only [if_neg he,if_neg (fun h => he (hm.mp h))] using hh

theorem markedWheel_spoke_typed_indicator
    (W:MarkedWheel tail head ktail khead m π b H₀ HK) (j:Bool) (v:V) (u:U):
    (if W.2.val=u then markedSpokeIndicator W.1.val j v else 0)=
      if Sum.inr (j,v,u)∈typedMarkedOccurrenceResources W then (1:ℝ) else 0:=by
  let f:=fun i:Fin (m+1)=>(decide (i=0),W.1.val i,W.2.val)
  have hf:Function.Injective f:=by
    intro i l h
    exact permutationSeparated_injective π b W.1.val W.1.property.1 (congrArg (fun s:Bool×V×U=>s.2.1) h)
  have hh:=injective_occurrence_sum f hf (j,v,u)
  have hmem:(j,v,u)∈Finset.univ.image f↔Sum.inr (j,v,u)∈typedMarkedOccurrenceResources W:=by
    rw [typedMarkedOccurrenceResources_spoke]
    simp only [Finset.mem_image,Finset.mem_univ,true_and,f]
  have hh' : (∑ i, if f i = (j,v,u) then (1:ℝ) else 0) =
      if Sum.inr (j,v,u) ∈ typedMarkedOccurrenceResources W then 1 else 0 := by
    by_cases he : Sum.inr (j,v,u) ∈ typedMarkedOccurrenceResources W
    · simpa only [if_pos he,if_pos (hmem.mpr he)] using hh
    · simpa only [if_neg he,if_neg (fun h => he (hmem.mp h))] using hh
  rw [←hh']
  dsimp only [f]
  rw [Fin.sum_univ_succ]
  by_cases hu:W.2.val=u
  · cases j <;> simp [markedSpokeIndicator,Prod.mk.injEq,hu,eq_comm]
  · have hu' : u ≠ W.2.val := Ne.symm hu
    cases j <;> simp [markedSpokeIndicator,Prod.mk.injEq,hu,hu']

end Oberwolfach
