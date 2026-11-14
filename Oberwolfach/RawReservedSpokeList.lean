module

public import Oberwolfach.MixedOutcomeOrdinarySpokeExclusion

@[expose] public section
/-! The manuscript's reserved colour-one ordinary labels. They have their
original fixed marginal probability and are disjoint from all old interval
labels and colour-two ordinary labels. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def rawReservedSpokeList {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Bool Bool) (w:U):Finset V:=
  rawIntervalOrdinaryOuter π d σ false w

theorem raw_reserved_spoke_list_avoids_old_labels
    {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ false) t) (w:U):
    let L:=rawReservedSpokeList π d σ w
    let root:=retainedAndRawIntervalRoot π d σ false true t J w
    Disjoint L (rawIntervalOrdinaryOuter π d σ true w) ∧
    ∀i (j:Fin (d+1)),(π^j.val) (root i)∉L:=by
  intro L root
  constructor
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    have hfalse:rawIntervalFamilyState π d σ (x,w)=some (Sum.inr false):=by
      simpa only [L,rawReservedSpokeList,rawIntervalOrdinaryOuter,Finset.mem_filter,Finset.mem_univ,true_and] using hx
    have htrue:rawIntervalFamilyState π d σ (x,w)=some (Sum.inr true):=by
      simpa only [rawIntervalOrdinaryOuter,Finset.mem_filter,Finset.mem_univ,true_and] using hy
    rw [hfalse] at htrue
    cases htrue
  · intro i j
    have hdis:=retained_and_raw_intervals_avoid_ordinary_spokes π d σ false true t J w false i
    intro hx
    apply Finset.disjoint_left.mp hdis _ hx
    unfold permutationWindow
    apply Finset.mem_image.mpr
    exact ⟨⟨j.val,by omega⟩,Finset.mem_univ _,rfl⟩
end Oberwolfach
