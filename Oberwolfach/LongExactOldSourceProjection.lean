module

public import Oberwolfach.LongSelectedOrientedSourceExactOld
public import Oberwolfach.LongSelectedOrientedSourceWithLoadAndMatching

@[expose] public section
/-! The exact-old source is a strengthening of the existing oriented source;
forgetting the exactness retains the original assumptions and witnesses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance exactOldSourceProjectionFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem long_exact_old_source_forget_exactness
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hU:0<Fintype.card U) (F:U→SimpleGraph (Fin n)) (P:SimpleGraph (Fin n))
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (H:Finset U) (A:Finset (Fin n)) (Kbad Used:SimpleGraph (Fin n)) (absorber:U→Finset (Fin n)) (δ:ℝ)
    (Extra:(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop):
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let e:{z // z∈T}↪_:=Function.Embedding.subtype _;
    ∀M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e),
    LongSelectedOrientedSourceExactOld hU F P π d m ℓ raw t Jret σ H A Kbad Used absorber δ Extra M→
    LongSelectedOrientedSourceWithLoadAndMatching hU F P π d m ℓ raw t Jret σ H A Kbad Used absorber δ Extra M:=by
  intro T e M hsource
  unfold LongSelectedOrientedSourceExactOld at hsource
  unfold LongSelectedOrientedSourceWithLoadAndMatching
  have ha:selectedOrientedSourceExactOldFin n=exactOldSourceProjectionFin n:=Subsingleton.elim _ _
  have hb:selectedOrientedSourceLoadMatchingFin n=exactOldSourceProjectionFin n:=Subsingleton.elim _ _
  have hc:selectedOrientedSourceExactOldFin K=exactOldSourceProjectionFin K:=Subsingleton.elim _ _
  have hd:selectedOrientedSourceLoadMatchingFin K=exactOldSourceProjectionFin K:=Subsingleton.elim _ _
  try rw [ha,hc] at hsource
  try rw [hb,hd]
  rcases hsource with ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,hload,pieces,hpieceEdge,hpieceArc,Pack,hExact,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra⟩
  exact ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,hload,pieces,hpieceEdge,hpieceArc,Pack,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra⟩
end Oberwolfach
