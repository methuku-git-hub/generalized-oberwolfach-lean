module

public import Oberwolfach.LongRawMatchingBufferedEmbedding
public import Oberwolfach.ActualResidualDataFromPacking
public import Oberwolfach.ActualApproxIntervalsOccupied
public import Oberwolfach.ActualFinalInteriorIdentification
public import Oberwolfach.ActualOldImageDirected

@[expose] public section
/-! Construct the residual-data record from the matching's physical selected
positions and immediately invoke the same-outcome buffered embedding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawPackedResidualDecEqFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_raw_packed_residual_embedding
    {N K:ℕ} {U X A B J:Type} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]
    [Fintype A] [Fintype B] [Fintype J] [DecidableEq A] [DecidableEq B] [DecidableEq J] [Nonempty (Fin N)]
    (F:SimpleGraph X) (hF:F.IsRegularOfDegree 2) (P₀:SimpleGraph (Fin N))
    (π:Equiv.Perm (Fin N)) (c d m:ℕ) (hc:3≤c) (hd:0<d) (hcm:c=m+1)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (ℓ:Fin K→ℕ) (raw:RawMarkedOutcome (Fin N) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t) (w:U)
    (index:A⊕B ≃ retainedAndRawIntervalIndex π d (fun e=>raw (Sum.inr e)) false true t Jret w)
    (u v:A⊕B→X) (P:∀i,F.Walk (u i) (v i)) (hp:∀i,(P i).IsPath)
    (hP:∀i j,i≠j→Disjoint (P i).support.toFinset (P j).support.toFinset)
    (hlen:∀i,(P i).length=c*d+4) (ext:∀i:A⊕B,Fin (c*d+5)↪X)
    (hsupp:∀i,(P i).support=List.ofFn (ext i))
    (hsrc:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (inner:∀a:A,Fin (c*d+1)↪X) (hinner:∀a k,inner a k=ext (.inl a) ⟨k.val+2,by omega⟩)
    (root:J→X) (C:∀j,F.Walk (root j) (root j)) (hcycle:∀j,(C j).IsCycle)
    (hC:∀i j,i≠j→Disjoint (C i).support.toFinset (C j).support.toFinset)
    (hcross:∀i j,Disjoint (P i).support.toFinset (C j).support.toFinset):
    let state:=longRawHubState P₀ π d raw true true
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    let targetRoot:=fun i=>retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true t Jret w (index i)
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    (∀x∈M,∀y∈M,x≠y→Disjoint (restrictedResourceSet (mixedCandidateResources R) e x)
      (restrictedResourceSet (mixedCandidateResources R) e y))→
    ∀(select:J↪LongRawSelectedOrdinary π d m ℓ e M),
    (∀j,ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M (select j)).1=(C j).length)→
    (∀j,(longRawSelectedOrdinaryWheel π d m ℓ e M (select j)).val.2=w)→
    let S:=longRawMarkedWheelsAtHub P₀ π d m ℓ raw true true M w
    let data:=actualResidualDataFromPacking F u v P hp hP c d hc hd hlen _ _ _ _ m (3*d) π
      (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true) S w targetRoot root C hcycle hC hcross
    ∃ψ:X→Fin N,
      Set.InjOn ψ (↑(data.oldDomain\bufferedPathStrictInterior (fun _=>c*d) inner):Set X) ∧
      (∀i (j:Fin (d+1)),bufferedMarker c d (ext i) j∈data.prescribed→
        ψ (bufferedMarker c d (ext i) j)=(π^j.val) (targetRoot i)) ∧
      (∀r:SelectedRunIndex data.s₂ data.d data.T,∀j,j≤r.2.val.2+1-r.2.val.1→
        ψ ((data.P r.1.val).getVert (2+data.c*(r.2.val.1+j)))=(π^(r.2.val.1+j)) (targetRoot r.1.val)) ∧
      (∀i∈data.s₂,∀j:Fin (d+1),∃x∈data.oldDomain\bufferedPathStrictInterior (fun _=>c*d) inner,
        ψ x=(π^j.val) (targetRoot i)) ∧
      ActualOldImageDirected data ψ (rawMixedPhysicalArc P₀ π d raw) ∧
      ActualOldPhysicalCoverage data ψ (longRawPhysicalHubRims P₀ π d m ℓ raw true true M w):=by
  intro state e R targetRoot M hmatch select hlength hhub S data
  let select':{j // j∈data.t}↪LongRawSelectedOrdinary π d m ℓ e M:=
    ⟨fun j=>select j.val,by intro a b h;apply Subtype.ext;exact select.injective h⟩
  have hlen':∀j,ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M (select' j)).1=(data.C j.val).length:=by
    intro j
    exact hlength j.val
  have hhub':∀j,(longRawSelectedOrdinaryWheel π d m ℓ e M (select' j)).val.2=w:=fun j=>hhub j.val
  have hT:∀i∈data.s₂,data.T i=packedPhysicalSpokePositions _ _ _ _ m (3*d) d π
      (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true) S w (targetRoot i):=by
    intro i _
    rfl
  have hCyc:data.t.biUnion (fun j=>(data.C j).support.toFinset)⊆data.Cembed:=by
    exact Finset.Subset.rfl
  have hfinal:∀a,(data.P ((firstSumIndexEquiv (B:=B)) a).val).support=List.ofFn (ext (.inl a)):=by
    intro a
    exact hsupp (.inl a)
  obtain ⟨ψ,hψ,hpres,hrun,hcyArc,hrunArc,hPhysical⟩:=long_raw_matching_buffered_embedding data P₀ π m hcm hnoshort ℓ raw t Jret w index M hmatch select' hlen' hhub' hT hF hCyc ext
    (fun i _=>hsupp i) hsrc firstSumIndexEquiv (fun a=>ext (.inl a)) inner hinner hfinal
  refine ⟨ψ,hψ,hpres,hrun,?_,⟨hcyArc,hrunArc⟩,hPhysical⟩
  have hOcc:=actual_approx_intervals_occupied data hF hCyc ext (fun i _=>hsupp i) π targetRoot ψ hpres hrun
  have heq:=actual_final_interiors_eq_buffered_strict data firstSumIndexEquiv (fun a=>ext (.inl a)) inner hinner hfinal
  rw [heq] at hOcc
  exact hOcc
end Oberwolfach
