module

public import Oberwolfach.MarkedStarRestrictionBalances
public import Oberwolfach.MarkedPackingFiniteBalance

@[expose] public section

/-! Subtracting the actual prescribed-edge wheel packing preserves the
balances at the deeper rows and hubs after temporary star reservation.
No balance elsewhere in the temporarily reduced host is required. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U]
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]
  {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {b m:ℕ} {H₀ HK:V→U→Prop}

theorem marked_local_balances_after_packing
    (A:Finset (E⊕K)) (S:Finset (V×U)) (T:Finset V) (W:Finset U)
    (hrows:∀ v∈T,
      (A.filter (fun a=>Sum.elim head khead a=v)).card=(A.filter (fun a=>Sum.elim tail ktail a=v)).card∧
      (A.filter (fun a=>Sum.elim head khead a=v)).card=(S.filter (fun z=>z.1=v)).card∧
      (A.filter (fun a=>Sum.elim head khead a=v∧markedArcType a=true)).card=
        (S.filter (fun z=>z.1=v∧HK z.1 z.2)).card)
    (hhubs:∀ u∈W,(S.filter (fun z=>z.2=u∧¬HK z.1 z.2)).card=
      m*(S.filter (fun z=>z.2=u∧HK z.1 z.2)).card)
    (hH:∀ v u,¬(H₀ v u∧HK v u))
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (hM:∀ C∈M,∀ D∈M,C≠D→Disjoint (markedWheelPhysicalResources C) (markedWheelPhysicalResources D))
    (hA:M.biUnion markedWheelArcs⊆A) (hS:M.biUnion markedWheelSpokePairs⊆S):
    let A':=A\M.biUnion markedWheelArcs
    let S':=S\M.biUnion markedWheelSpokePairs
    (∀ v∈T,
      (A'.filter (fun a=>Sum.elim head khead a=v)).card=(A'.filter (fun a=>Sum.elim tail ktail a=v)).card∧
      (A'.filter (fun a=>Sum.elim head khead a=v)).card=(S'.filter (fun z=>z.1=v)).card∧
      (A'.filter (fun a=>Sum.elim head khead a=v∧markedArcType a=true)).card=
        (S'.filter (fun z=>z.1=v∧HK z.1 z.2)).card)∧
    (∀ u∈W,(S'.filter (fun z=>z.2=u∧¬HK z.1 z.2)).card=
      m*(S'.filter (fun z=>z.2=u∧HK z.1 z.2)).card):=by
  have hdiv:=marked_packing_finite_divisible hH M hM
  dsimp only
  constructor
  · intro v hv
    obtain ⟨hd,hr,hm⟩:=hrows v hv
    refine ⟨?_,?_,?_⟩
    · rw [finite_filter_sdiff_card A _ hA,finite_filter_sdiff_card A _ hA,hd,hdiv.directed v]
    · rw [finite_filter_sdiff_card A _ hA,finite_filter_sdiff_card S _ hS,hr,hdiv.row v]
    · rw [finite_filter_sdiff_card A _ hA,finite_filter_sdiff_card S _ hS,hm,hdiv.marked v]
  · intro u hu
    rw [finite_filter_sdiff_card S _ hS,finite_filter_sdiff_card S _ hS,
      hhubs u hu,hdiv.hub u,Nat.mul_sub_left_distrib]

theorem marked_reserved_star_and_packing_deep_balances
    (A C:Finset (E⊕K)) (S R:Finset (V×U)) (hCA:C⊆A) (hRS:R⊆S)
    (houter:MarkedRemainderDivisible tail head ktail khead HK A S m)
    (hinner:MarkedRemainderDivisible tail head ktail khead HK C R m)
    (T:Finset V) (W:Finset U) (hH:∀ v u,¬(H₀ v u∧HK v u))
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (hM:∀ C∈M,∀ D∈M,C≠D→Disjoint (markedWheelPhysicalResources C) (markedWheelPhysicalResources D))
    (hA:M.biUnion markedWheelArcs⊆A\C.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T))
    (hS:M.biUnion markedWheelSpokePairs⊆S\R.filter (fun z=>z.1∈T∨z.2∈W)):
    let A':=(A\C.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T))\M.biUnion markedWheelArcs
    let S':=(S\R.filter (fun z=>z.1∈T∨z.2∈W))\M.biUnion markedWheelSpokePairs
    (∀ v∈T,
      (A'.filter (fun a=>Sum.elim head khead a=v)).card=(A'.filter (fun a=>Sum.elim tail ktail a=v)).card∧
      (A'.filter (fun a=>Sum.elim head khead a=v)).card=(S'.filter (fun z=>z.1=v)).card∧
      (A'.filter (fun a=>Sum.elim head khead a=v∧markedArcType a=true)).card=
        (S'.filter (fun z=>z.1=v∧HK z.1 z.2)).card)∧
    (∀ u∈W,(S'.filter (fun z=>z.2=u∧¬HK z.1 z.2)).card=
      m*(S'.filter (fun z=>z.2=u∧HK z.1 z.2)).card):=by
  obtain ⟨hr,hu⟩:=marked_remove_reserved_star_deep_balances A C S R hCA hRS houter hinner T W
  exact marked_local_balances_after_packing _ _ T W hr hu hH M hM hA hS

end Oberwolfach
