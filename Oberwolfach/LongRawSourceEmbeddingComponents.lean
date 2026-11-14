module

public import Oberwolfach.LongRawAssignedSourceComponents
public import Oberwolfach.LongRawComponentAssignmentFromMaps
public import Oberwolfach.LongAssignedActualIntervalCapacityDecidable
public import Oberwolfach.LongAssignedPaddedLengths

@[expose] public section
/-! Actual long source paths and their old embeddings from one matching,
the original class hypothesis, and the same-outcome hub start counts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawSourceEventComponentsDecEqFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_raw_source_embeddings_from_matching_and_starts_with_components
    {N K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin N)]
    (F:U→SimpleGraph (Fin N)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (E:∀w (D:(F w).ConnectedComponent),SimpleGraph.cycleGraph (Fintype.card D) ≃g D.toSimpleGraph)
    (Allowed:Set ℕ) (hAllowed:∀w,AllowedCycleLengths (F w) Allowed)
    (hn:0<N) (hK:3≤K) (hclass:∀w,factorPreparationClass (F w) K=none)
    (P₀:SimpleGraph (Fin N)) (π:Equiv.Perm (Fin N)) (d m:ℕ) (hd:2≤d) (hm:7≤m)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (θ:ℝ) (hθ:0<θ)
    (hcut:5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K+1)≤θ/2)
    (hlarge:8*((m:ℝ)+1)/θ<(N:ℝ)^((1:ℝ)/4))
    (raw:RawMarkedOutcome (Fin N) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (hcounts:∀w g,|rawIntervalHubStartCount π d g (fun e=>raw (Sum.inr e)) w-
      (N:ℝ)*longAssignedIntervalProbability F hF K m θ w g/d|<(N:ℝ)^(3/4:ℝ)/d):
    let ℓ:=longAssignedPaddedLength (K:=K)
    let state:=longRawHubState P₀ π d raw true true
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    (∀x∈M,∀y∈M,x≠y→Disjoint (restrictedResourceSet (mixedCandidateResources R) e x)
      (restrictedResourceSet (mixedCandidateResources R) e y))→
    LongRawOrdinaryComponentMapsProperty F π d m ℓ e M→
    ∃assign:LongRawSelectedOrdinary π d m ℓ e M↪(Σw,(F w).ConnectedComponent),
      (∀a,(assign a).1=(longRawSelectedOrdinaryWheel π d m ℓ e M a).val.2) ∧
      (∀a,Fintype.card (assign a).2=ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a).1) ∧
    ∀w:U,
      let A:=retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w
      let B:={a:Fin N // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) a true}
      let I:={C:(F w).ConnectedComponent // K<Fintype.card C}
      let components:I↪(F w).ConnectedComponent:=Function.Embedding.subtype _
      let J:={a:LongRawSelectedOrdinary π d m ℓ e M // (assign a).1=w}
      let S:=longRawMarkedWheelsAtHub P₀ π d m ℓ raw true true M w
      let root:=retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true t Jret w
      ∃(block:A⊕B↪LongReservedBlockIndex (F w) components (m+1) d)
        (data:ActualResidualData (K:=A⊕B) (J:=J) (F w))
        (ext:∀i:A⊕B,Fin ((m+1)*d+5)↪Fin N) (inner:∀a:A,Fin ((m+1)*d+1)↪Fin N) (ψ:Fin N→Fin N),
        data.c=m+1 ∧ data.d=d ∧ data.s₁=firstSumIndices ∧ data.s₂=secondSumIndices ∧ data.t=Finset.univ ∧
        data.Cembed=data.t.biUnion (fun j=>(data.C j).support.toFinset) ∧
        (∀i,data.T i=packedPhysicalSpokePositions _ _ _ _ m (3*d) d π
          (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true) S w (root i)) ∧
        (∀i,(data.P i).support=List.ofFn (ext i)) ∧
        (∀i,ext i=longReservedSigmaBlock (F w) components (m+1) d (fun k=>E w (components k)) (block i) d (le_refl _)) ∧
        (∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j))) ∧
        (∀a k,inner a k=ext (.inl a) ⟨k.val+2,by omega⟩) ∧
        (∀j:J,(data.C j).length=ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M j.val).1) ∧
        (∀j:J,∀k<(data.C j).length,factorCycleOrientation (F w) (E w) ((data.C j).getVert k)=(data.C j).getVert (k+1)) ∧
        Set.InjOn ψ (↑(data.oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) inner):Set (Fin N)) ∧
        (∀i (j:Fin (d+1)),bufferedMarker (m+1) d (ext i) j∈data.prescribed→
          ψ (bufferedMarker (m+1) d (ext i) j)=(π^j.val) (root i)) ∧
        (∀i∈data.s₂,∀j:Fin (d+1),∃x∈data.oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) inner,
          ψ x=(π^j.val) (root i)) ∧
        ActualOldImageDirected data ψ (rawMixedPhysicalArc P₀ π d raw) ∧
        ActualOldArcContainment data ψ (E w) (rawMixedPhysicalArc P₀ π d raw) ∧
        ActualOldPhysicalCoverage data ψ (longRawPhysicalHubRims P₀ π d m ℓ raw true true M w) ∧
        ActualOldArcContainment data ψ (E w) (fun x y=>({x,y}:Finset (Fin N))∈longRawPhysicalHubRims P₀ π d m ℓ raw true true M w) ∧
        (∀x,x∈data.oldDomain→x∉bufferedPathFullDomain (fun _=>(m+1)*d) inner→
          ψ x∉markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w=>d) Subtype.val) ∧
        Disjoint ((data.oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) inner).image ψ)
          (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w) ∧
        (∀j:J,(data.C j).toSubgraph.verts=
          (assignedComponentAtHub F (fun a=>(assign a).1) (fun a=>(assign a).2) w j).supp):=by
  intro ℓ state e R M hmatch hmaps
  obtain ⟨assign,hhub,hsize⟩:=long_raw_assignment_from_component_maps F π d m ℓ e M hmaps
  refine ⟨assign,hhub,hsize,?_⟩
  intro w A B I components J S root
  let index:A⊕B ≃ retainedAndRawIntervalIndex π d (fun e=>raw (Sum.inr e)) false true t Jret w:=Equiv.refl _
  have hindex:∀b:B,∃a:{a:Fin N // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) a true},index (.inr b)=Sum.inr a:=fun b=>⟨b,rfl⟩
  have hcapacity:=long_assigned_actual_interval_capacity_decidable F hF Allowed hAllowed hn (by omega) hclass π d m (by omega) θ hθ
    (fun e=>raw (Sum.inr e)) t Jret w index hcut hlarge (hcounts w)
  have hlong:∀i:I,K+1≤Fintype.card (components i):=fun i=>Nat.succ_le_iff.mpr i.property
  have hshort:∀a:LongRawSelectedOrdinary π d m ℓ e M,ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a).1<K+1:=by
    intro a
    exact Nat.lt_succ_of_le (long_assigned_padded_length_upper hK _)
  exact long_raw_assigned_source_embedding_with_reserved_spokes_and_components F hF E P₀ π (m+1) d m (K+1) (by omega) (by omega) rfl hnoshort ℓ raw t Jret w index hindex components hlong hcapacity M hmatch assign hhub hsize hshort
end Oberwolfach
