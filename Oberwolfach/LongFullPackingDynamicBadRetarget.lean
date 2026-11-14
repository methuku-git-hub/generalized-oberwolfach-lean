module

public import Oberwolfach.LongClassInnerRequiredRepair
public import Oberwolfach.LongExactOldDynamicBadRetarget
public import Oberwolfach.MatchingExactPackingRepairVanishes

@[expose] public section
/-! The dynamic required graph is the original required graph for the actual
full matching packing, so no additional local degree allowance is needed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance fullPackingDynamicRetargetFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem long_full_packing_dynamic_bad_retarget
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hU:0<Fintype.card U) (F:U→SimpleGraph (Fin n)) (P:SimpleGraph (Fin n))
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (H:Finset U) (A:Finset (Fin n)) (Sclass Kbase Used:SimpleGraph (Fin n))
    (absorber:U→Finset (Fin n)) (δ:ℝ)
    (Extra:SimpleGraph (Fin n)→(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop):
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let e:{z // z∈T}↪_:=Function.Embedding.subtype _
    let Kplus:=fun Pack:Finset (Sym2 (Fin n))=>longClassInnerRequiredRepair Sclass Used Kbase A Pack
    let ExtraFull:=fun Old Pack=>Extra Kbase Old Pack ∧ Pack=Used.edgeFinset
    let ExtraDynamic:=fun Old Pack=>Extra (Kplus Pack) Old Pack ∧ Pack=Used.edgeFinset
    ∀M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e),
    LongSelectedOrientedSourceExactOld hU F P π d m ℓ raw t Jret σ H A Kbase Used absorber δ ExtraFull M→
    LongSelectedOrientedSourceDynamicBad hU F P π d m ℓ raw t Jret σ H A Kplus Used absorber δ ExtraDynamic M:=by
  intro T e Kplus ExtraFull ExtraDynamic M hsource
  apply long_exact_old_dynamic_bad_retarget hU F P π d m ℓ raw t Jret σ H A Kbase Used Kplus absorber δ δ 0 ExtraFull ExtraDynamic ?_ ?_ ?_ M hsource
  · intro Old Pack hfull v hv
    have heq:Kplus Pack=Kbase:=matching_exact_class_packing_repair_vanishes Sclass Used Kbase A Pack hfull.2
    simp only [add_zero]
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro x hx
    simp only [SimpleGraph.mem_neighborFinset] at hx ⊢
    exact heq ▸ hx
  · simp
  · intro Old Pack hsub hfull
    dsimp only [ExtraDynamic]
    constructor
    · dsimp only [Kplus,longClassInnerRequiredRepair]
      rw [matching_exact_class_packing_repair_vanishes Sclass Used Kbase A Pack hfull.2]
      exact hfull.1
    · exact hfull.2
end Oberwolfach
