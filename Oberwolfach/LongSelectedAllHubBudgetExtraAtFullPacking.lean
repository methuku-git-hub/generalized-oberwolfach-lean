module

public import Oberwolfach.LongSelectedRetainedClassDynamicSameBalancedAllHubBudget

@[expose] public section
/-! The extra matching data in the selected balanced witness belongs to the
same full packing returned by the residual and correction constructions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance selectedAllHubBudgetExtraFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem long_selected_all_hub_budget_extra_at_full_packing
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hU:0<Fintype.card U) (F:U→SimpleGraph (Fin n)) (P:SimpleGraph (Fin n))
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (H:Finset U) (I:Finset (Fin n)) (Sclass:SimpleGraph (Fin n))
    (Kbad:Finset (Sym2 (Fin n))→SimpleGraph (Fin n)) (Used DelG Reserve:SimpleGraph (Fin n))
    (absorber:U→Finset (Fin n)) (δ:ℝ) (Mhost:Fin n→Fin n→ℕ) (Dhost:Fin n→Fin n→Prop)
    (Extra:(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop) (ρ₀ θ δglobal Pbound:ℝ)
    (hPackEq:∀Old Pack,Extra Old Pack→Pack=Used.edgeFinset):
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let e:{z // z∈T}↪_:=Function.Embedding.subtype _
    ∀M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e),
    LongSelectedRetainedClassDynamicSourceSameBalancedAllHubBudget hU F P π d m ℓ raw t Jret σ H I Sclass Kbad Used DelG Reserve absorber δ Mhost Dhost Extra ρ₀ θ δglobal Pbound M→
    ∀Pack:Finset (Sym2 (Fin n)),Pack=Used.edgeFinset→∃Old,Extra Old Pack :=by
  intro T e M hsource Pack hPack
  letI:Nonempty U:=Fintype.card_pos_iff.mp hU
  have hdec:selectedRetainedClassDynamicSameBalancedAllHubBudgetFin n=selectedAllHubBudgetExtraFin n:=Subsingleton.elim _ _
  have hdecK:selectedRetainedClassDynamicSameBalancedAllHubBudgetFin K=selectedAllHubBudgetExtraFin K:=Subsingleton.elim _ _
  try rw [hdec] at hsource
  try rw [hdecK] at hsource
  rcases hsource with ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,hpres,pieces,hpieceEdge,hpieceArc,Pack₀,hExact,hload,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra,rest⟩
  have heq:Pack₀=Pack:=(hPackEq _ _ hExtra).trans hPack.symm
  refine ⟨fun w=>((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)).image (ψ w),?_⟩
  rw [←heq]
  exact hExtra
end Oberwolfach
