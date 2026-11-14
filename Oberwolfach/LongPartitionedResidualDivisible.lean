module

public import Oberwolfach.MarkedPartitionedOccurrenceDegree
public import Oberwolfach.MarkedOccurrenceDegreesDivisible
public import Oberwolfach.LongResidualMarkedSpokeBalance

@[expose] public section
/-! A constant corrected marked indegree makes the physical and typed head
counts agree after the permutation shift.  Together with the remaining row and
hub identities this gives the exact finite divisibility required downstream. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
local instance partitionedDivisibleDecEq : DecidableEq V := Classical.decEq V
local instance partitionedDivisibleArc (P:V×V→Prop):DecidableEq {e:V×V // P e}:=Classical.decEq _
local instance partitionedDivisibleArcFinite (P:V×V→Prop):Fintype {e:V×V // P e}:=Fintype.ofFinite _
local instance partitionedDivisibleOrdFinite (P:V×V→Prop) (M:Finset {e:V×V // P e}):Fintype (residualOrdinaryArc P M):=by
  change Fintype {e:{a:V×V // P a} // e∉M}
  exact Fintype.ofFinite _
local instance partitionedDivisibleMarkFinite (P:V×V→Prop) (M:Finset {e:V×V // P e}):Fintype (residualMarkedArc P M):=by
  change Fintype {e:{a:V×V // P a} // e∈M}
  exact Fintype.ofFinite _

theorem long_partitioned_residual_divisible
    (P:V×V→Prop) (M:Finset {e:V×V // P e}) (π:Equiv.Perm V) (d m:ℕ) (hd:1≤d)
    (hnoshort:∀x l,0<l→l<d→(π^l) x≠x)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (g:Γ) (j:Color) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ g) t)
    (H₀:V→U→Prop)
    (hH:∀v u,¬(H₀ v u∧retainedRawMarkedSpokes π d σ g t J g j true v u))
    (hmarked:∀v,directedInCount P M v=d*t)
    (hphysical:∀v,occurrenceDegree (fun e:{a:V×V // P a}=>e.val.1) v=
      occurrenceDegree (fun e:{a:V×V // P a}=>e.val.2) v)
    (hrow:∀v,occurrenceDegree (fun e:{a:V×V // P a}=>e.val.1) v=
      (∑u,if H₀ v u then (1:ℝ) else 0)+
      (∑u,if retainedRawMarkedSpokes π d σ g t J g j true v u then (1:ℝ) else 0))
    (hhub:∀u,(∑v,if H₀ v u then (1:ℝ) else 0)=(m:ℝ)*
      (∑v,if retainedRawMarkedSpokes π d σ g t J g j true v u then (1:ℝ) else 0)):
    MarkedRemainderDivisible
      (fun e:residualOrdinaryArc P M=>e.val.val.1) (fun e=>e.val.val.2)
      (fun e:residualMarkedArc P M=>e.val.val.1) (fun e=>π.symm e.val.val.2)
      (retainedRawMarkedSpokes π d σ g t J g j true) Finset.univ
      (Finset.univ.filter (fun z:V×U=>H₀ z.1 z.2∨retainedRawMarkedSpokes π d σ g t J g j true z.1 z.2)) m:=by
  let tail:=fun e:residualOrdinaryArc P M=>e.val.val.1
  let head:=fun e:residualOrdinaryArc P M=>e.val.val.2
  let ktail:=fun e:residualMarkedArc P M=>e.val.val.1
  let khead:=fun e:residualMarkedArc P M=>π.symm e.val.val.2
  have ht:∀v,occurrenceDegree (Sum.elim tail ktail) v=occurrenceDegree (fun e:{a:V×V // P a}=>e.val.1) v:=by
    intro v
    rw [occurrenceDegree_sum]
    exact partitioned_occurrence_degree_sum P M (fun e=>e.val.1) v
  have hh:∀v,occurrenceDegree (Sum.elim head khead) v=occurrenceDegree (fun e:{a:V×V // P a}=>e.val.2) v:=by
    intro v
    rw [occurrenceDegree_sum]
    have hp:=partitioned_occurrence_degree_sum P M (fun e=>e.val.2) v
    have hs:=partitioned_marked_head_degree P M π v
    have hi:=partitioned_marked_head_degree P M (Equiv.refl V) v
    have hs':occurrenceDegree khead v=((d*t:ℕ):ℝ):=by
      simpa only [khead,hmarked] using hs
    have hi':occurrenceDegree (fun e:residualMarkedArc P M=>e.val.val.2) v=((d*t:ℕ):ℝ):=by
      simpa only [Equiv.refl_symm,Equiv.refl_apply,hmarked] using hi
    have he:occurrenceDegree khead v=occurrenceDegree (fun e:residualMarkedArc P M=>e.val.val.2) v:=hs'.trans hi'.symm
    linarith [hp,he]
  apply marked_occurrence_degrees_divisible tail head ktail khead H₀ (retainedRawMarkedSpokes π d σ g t J g j true) m hH
  · intro v
    rw [ht,hh]
    exact hphysical v
  · exact long_residual_marked_head_spoke_balance P M π d hd hnoshort σ g j t J hmarked
  · intro v
    rw [ht]
    exact hrow v
  · exact hhub
end Oberwolfach
