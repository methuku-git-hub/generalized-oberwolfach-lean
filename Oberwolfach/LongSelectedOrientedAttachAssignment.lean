module

public import Oberwolfach.LongSelectedOrientedSourceWithMatchingCapacity

@[expose] public section
/-! Attach an assignment to the same residual source, using the actual old
vertices and the actual packed edges already carried by that source. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance selectedOrientedAttachFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem long_selected_oriented_source_attach_assignment
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hU:0<Fintype.card U) (F:U→SimpleGraph (Fin n)) (P:SimpleGraph (Fin n))
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (H:Finset U) (A:Finset (Fin n)) (Kbad Used:SimpleGraph (Fin n)) (absorber:U→Finset (Fin n)) (δ ρ₀:ℝ)
    (Extra₀ Extra₁:(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop):
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let e:{z // z∈T}↪_:=Function.Embedding.subtype _;
    ∀M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e),
      LongSelectedOrientedSourceWithLoadMatchingCapacity hU F P π d m ℓ raw t Jret σ H A Kbad Used absorber δ Extra₀ ρ₀ M→
      (∀Old Pack,(∀w,Disjoint (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w) (Old w))→
        Pack⊆Used.edgeFinset→Extra₀ Old Pack→Extra₁ Old Pack)→
      LongSelectedOrientedSourceWithLoadMatchingCapacity hU F P π d m ℓ raw t Jret σ H A Kbad Used absorber δ Extra₁ ρ₀ M:=by
  intro T e M hsource himp
  unfold LongSelectedOrientedSourceWithLoadMatchingCapacity at hsource ⊢
  have hdec:selectedOrientedMatchingCapacityFin n=selectedOrientedAttachFin n:=Subsingleton.elim _ _
  have hdecK:selectedOrientedMatchingCapacityFin K=selectedOrientedAttachFin K:=Subsingleton.elim _ _
  try rw [hdec] at hsource ⊢
  try rw [hdecK] at hsource ⊢
  rcases hsource with ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,hload,pieces,hpieceEdge,hpieceArc,Pack,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra,hcapacity⟩
  have hreserved:∀w,Disjoint (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w)
      (((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)).image (ψ w)):=by
    intro w
    rcases hprops w with ⟨_,_,_,_,_,_,_,_,_,_,_,hres,_,_,_,_,_,_,_,_,_,_,_⟩
    exact hres.symm
  refine ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,hload,pieces,hpieceEdge,hpieceArc,Pack,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,?_,hcapacity⟩
  exact himp _ _ hreserved hUsed hExtra
end Oberwolfach
