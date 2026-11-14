module

public import Oberwolfach.LongSelectedRetainedSourceDynamicGlobalLoad

@[expose] public section
/-! Strengthen the auxiliary predicate without changing the exact old
packing, its dynamic required graph, or any of the source witnesses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance retainedDynamicGlobalExtraMonoFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem long_retained_dynamic_global_extra_mono
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hU:0<Fintype.card U) (F:U→SimpleGraph (Fin n)) (P:SimpleGraph (Fin n))
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (H:Finset U) (A:Finset (Fin n)) (Kbad:Finset (Sym2 (Fin n))→SimpleGraph (Fin n))
    (Used:SimpleGraph (Fin n)) (absorber:U→Finset (Fin n)) (δ:ℝ)
    (ExtraOld ExtraNew:(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop) (ρ₀ θ δglobal:ℝ)
    (hExtra:∀Old Pack,ExtraOld Old Pack→ExtraNew Old Pack):
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let e:{z // z∈T}↪_:=Function.Embedding.subtype _;
    ∀M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e),
    LongSelectedRetainedSourceDynamicGlobalLoad hU F P π d m ℓ raw t Jret σ H A Kbad Used absorber δ ExtraOld ρ₀ θ δglobal M→
    LongSelectedRetainedSourceDynamicGlobalLoad hU F P π d m ℓ raw t Jret σ H A Kbad Used absorber δ ExtraNew ρ₀ θ δglobal M:=by
  intro T e M hsource
  unfold LongSelectedRetainedSourceDynamicGlobalLoad at hsource ⊢
  have hdec:selectedRetainedDynamicGlobalLoadFin n=retainedDynamicGlobalExtraMonoFin n:=Subsingleton.elim _ _
  have hdecK:selectedRetainedDynamicGlobalLoadFin K=retainedDynamicGlobalExtraMonoFin K:=Subsingleton.elim _ _
  try rw [hdec,hdecK] at hsource ⊢
  rcases hsource with ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,pieces,hpieceEdge,hpieceArc,Pack,hExact,hload,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hold,hcapacity,hupper,hglobal⟩
  exact ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,pieces,hpieceEdge,hpieceArc,Pack,hExact,hload,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra _ Pack hold,hcapacity,hupper,hglobal⟩
end Oberwolfach
