module

public import Oberwolfach.OrdinaryUncoveredTargetColumnFromStates

@[expose] public section

/-! Local unassigned-column concentration and the matching column error
bound the actual target load at a vertex. -/
set_option autoImplicit false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_uncovered_target_column_from_tests
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Bool Bool)
    (Inner:Finset V) (Hubs:Finset U) (Old:U→Finset V)
    (hno:∀w x,¬rawIntervalColouredStart π d (fun e=>σ (w,e)) x false)
    (happrox:∀w x,rawIntervalFamilyState π d σ (x,w)=some (Sum.inl true)→x∈Old w)
    (q s:U→Bool→ℝ) (θ error:ℝ)
    (hslack:∀w,1-(∑g,q w g)-(∑j,s w j)≤2*θ)
    (hlocal:∀v∈Inner,|rawIntervalUnassignedColumnCount π d σ v Hubs-
      ∑w∈Hubs,(1-(∑g,q w g)-(∑j,s w j))|<(Inner.card:ℝ)^(3/4:ℝ))
    (hcolumn:∀v,(((Finset.univ:Finset U).filter (fun w=>v∈ordinaryUnusedTrueSpokes π d σ Old w)).card:ℝ)≤error):
    ∀v∈Inner,(((Finset.univ:Finset U).filter (fun w=>v∈
      ordinaryInnerSpokeTargets Inner Hubs (fun x u=>x∈rawReservedSpokeList π d σ u) w\Old w)).card:ℝ)≤
      2*θ*Hubs.card+(Inner.card:ℝ)^(3/4:ℝ)+error :=by
  intro v hv
  have ht:=ordinary_uncovered_target_column_from_states π d σ Inner Hubs Old hno happrox v
  have hsum:(∑w∈Hubs,(1-(∑g,q w g)-(∑j,s w j)))≤(Hubs.card:ℝ)*(2*θ):=by
    calc
      _ ≤ ∑_w∈Hubs,2*θ:=Finset.sum_le_sum (by intro w hw;exact hslack w)
      _ = _ :=by simp
  have hdev:rawIntervalUnassignedColumnCount π d σ v Hubs-
      ∑w∈Hubs,(1-(∑g,q w g)-(∑j,s w j))<(Inner.card:ℝ)^(3/4:ℝ):=
    (abs_lt.mp (hlocal v hv)).2
  nlinarith [hcolumn v]
end Oberwolfach
