module

public import Oberwolfach.OrderedOrdinaryWheelGeometry
public import Oberwolfach.TypedMarkedIncidenceIndicators

@[expose] public section
/-! Each spoke or directed rim request occurs at most once in a separated
ordered cycle. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {r b:ℕ} {π:Equiv.Perm V}

theorem orderedOrdinary_spoke_indicator (W:OrderedOrdinaryWheel (U:=U) π b r) (v:V) (u:U):
    (if W.2=u then ∑ i:Fin r,if W.1.val i=v then (1:ℝ) else 0 else 0)=
      if Sum.inr (v,u)∈orderedOrdinaryResources W then 1 else 0:=by
  let f:=fun i:Fin r=>(W.1.val i,W.2)
  have hf:Function.Injective f:=by
    intro i j h
    exact permutationSeparated_injective π b W.1.val W.1.property (congrArg Prod.fst h)
  have hh:=injective_occurrence_sum f hf (v,u)
  have hmem:(v,u)∈Finset.univ.image f ↔ Sum.inr (v,u)∈orderedOrdinaryResources W:=by
    rw [orderedOrdinaryResources_spoke]
    simp [f]
  have hh':(∑ i,if f i=(v,u) then (1:ℝ) else 0)=
      if Sum.inr (v,u)∈orderedOrdinaryResources W then 1 else 0:=by
    by_cases he:Sum.inr (v,u)∈orderedOrdinaryResources W
    · simpa only [if_pos he,if_pos (hmem.mpr he)] using hh
    · simpa only [if_neg he,if_neg (fun h=>he (hmem.mp h))] using hh
  rw [←hh']
  by_cases hu:W.2=u
  · simp [f,Prod.mk.injEq,hu]
  · have hu':u≠W.2:=Ne.symm hu
    simp [f,Prod.mk.injEq,hu,hu']

theorem orderedOrdinary_rim_indicator (W:OrderedOrdinaryWheel (U:=U) π b r) (hr:3≤r) (x y:V):
    (∑ i:Fin r,if W.1.val i=x ∧ W.1.val (cycleNext i)=y then (1:ℝ) else 0)=
      if Sum.inl (x,y)∈orderedOrdinaryResources W then 1 else 0:=by
  let f:=fun i:Fin r=>(W.1.val i,W.1.val (cycleNext i))
  have hf:Function.Injective f:=by
    intro i j h
    have hs:=congrArg (fun e:V×V=>s(e.1,e.2)) h
    exact orderedOrdinaryPhysical_edge_injective hr W hs
  have hh:=injective_occurrence_sum f hf (x,y)
  have hmem:(x,y)∈Finset.univ.image f ↔ Sum.inl (x,y)∈orderedOrdinaryResources W:=by
    rw [orderedOrdinaryResources_rim]
    simp [f]
  have hh':(∑ i,if f i=(x,y) then (1:ℝ) else 0)=
      if Sum.inl (x,y)∈orderedOrdinaryResources W then 1 else 0:=by
    by_cases he:Sum.inl (x,y)∈orderedOrdinaryResources W
    · simpa only [if_pos he,if_pos (hmem.mpr he)] using hh
    · simpa only [if_neg he,if_neg (fun h=>he (hmem.mp h))] using hh
  rw [←hh']
  apply Finset.sum_congr rfl
  intro i _
  simp [f,Prod.mk.injEq]
end Oberwolfach
