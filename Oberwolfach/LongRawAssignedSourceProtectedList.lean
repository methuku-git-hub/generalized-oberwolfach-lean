module

public import Oberwolfach.GlobalAssignmentReservedFamilies
public import Oberwolfach.LongRawPackedResidualProtectedList
public import Oberwolfach.ActualOldArcContainment

@[expose] public section
/-! Build the actual reserved source families and residual data from the
same globally assigned mixed matching, then construct the old embedding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawAssignedSourceProtectedListDecEqFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_raw_assigned_source_embedding_with_protected_list
    {N K:ℕ} {U X I A B:Type} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]
    [Fintype I] [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [Nonempty (Fin N)]
    (F:U→SimpleGraph X) (hF:∀w,(F w).IsRegularOfDegree 2)
    (E:∀w (D:(F w).ConnectedComponent),SimpleGraph.cycleGraph (Fintype.card D) ≃g D.toSimpleGraph)
    (P₀:SimpleGraph (Fin N)) (π:Equiv.Perm (Fin N)) (c d m cutoff:ℕ) (hc:3≤c) (hd:0<d) (hcm:c=m+1)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (ℓ:Fin K→ℕ) (raw:RawMarkedOutcome (Fin N) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t) (w:U)
    (index:A⊕B ≃ retainedAndRawIntervalIndex π d (fun e=>raw (Sum.inr e)) false true t Jret w)
    (hindex:∀b:B,∃a:{a:Fin N // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) a true},index (.inr b)=Sum.inr a)
    (longComponents:I↪(F w).ConnectedComponent)
    (hlong:∀i,cutoff≤Fintype.card (longComponents i))
    (hcapacity:Fintype.card (A⊕B)≤∑i:I,Fintype.card (longComponents i)/(c*d+5)):
    let state:=longRawHubState P₀ π d raw true true
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    let targetRoot:=fun i=>retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true t Jret w (index i)
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    (∀x∈M,∀y∈M,x≠y→Disjoint (restrictedResourceSet (mixedCandidateResources R) e x)
      (restrictedResourceSet (mixedCandidateResources R) e y))→
    ∀(assign:LongRawSelectedOrdinary π d m ℓ e M↪(Σw,(F w).ConnectedComponent)),
    (∀a,(assign a).1=(longRawSelectedOrdinaryWheel π d m ℓ e M a).val.2)→
    (∀a,Fintype.card (assign a).2=ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a).1)→
    (∀a,ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a).1<cutoff)→
    let J:={a:LongRawSelectedOrdinary π d m ℓ e M // (assign a).1=w}
    let S:=longRawMarkedWheelsAtHub P₀ π d m ℓ raw true true M w
    ∃(block:A⊕B↪LongReservedBlockIndex (F w) longComponents c d)
      (data:ActualResidualData (K:=A⊕B) (J:=J) (F w))
      (ext:∀i:A⊕B,Fin (c*d+5)↪X) (inner:∀a:A,Fin (c*d+1)↪X) (ψ:X→Fin N),
      data.c=c ∧ data.d=d ∧ data.s₁=firstSumIndices ∧ data.s₂=secondSumIndices ∧ data.t=Finset.univ ∧
      data.Cembed=data.t.biUnion (fun j=>(data.C j).support.toFinset) ∧
      (∀i,data.T i=packedPhysicalSpokePositions _ _ _ _ m (3*d) d π
        (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true) S w (targetRoot i)) ∧
      (∀i,(data.P i).support=List.ofFn (ext i)) ∧
      (∀i,ext i=longReservedSigmaBlock (F w) longComponents c d (fun k=>E w (longComponents k)) (block i) d (le_refl _)) ∧
      (∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j))) ∧
      (∀a k,inner a k=ext (.inl a) ⟨k.val+2,by omega⟩) ∧
      (∀j:J,(data.C j).length=ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M j.val).1) ∧
      (∀j:J,∀k<(data.C j).length,factorCycleOrientation (F w) (E w) ((data.C j).getVert k)=(data.C j).getVert (k+1)) ∧
      Set.InjOn ψ (↑(data.oldDomain\bufferedPathStrictInterior (fun _=>c*d) inner):Set X) ∧
      (∀i (j:Fin (d+1)),bufferedMarker c d (ext i) j∈data.prescribed→
        ψ (bufferedMarker c d (ext i) j)=(π^j.val) (targetRoot i)) ∧
      (∀i∈data.s₂,∀j:Fin (d+1),∃x∈data.oldDomain\bufferedPathStrictInterior (fun _=>c*d) inner,
        ψ x=(π^j.val) (targetRoot i)) ∧
      ActualOldImageDirected data ψ (rawMixedPhysicalArc P₀ π d raw) ∧
      ActualOldArcContainment data ψ (E w) (rawMixedPhysicalArc P₀ π d raw) ∧
      ActualOldPhysicalCoverage data ψ (longRawPhysicalHubRims P₀ π d m ℓ raw true true M w) ∧
      ActualOldArcContainment data ψ (E w) (fun x y=>({x,y}:Finset (Fin N))∈longRawPhysicalHubRims P₀ π d m ℓ raw true true M w) ∧
      (∀x,x∈data.oldDomain→x∉bufferedPathFullDomain (fun _=>c*d) inner→
        ψ x∉markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w=>d) Subtype.val) ∧
      Disjoint ((data.oldDomain\bufferedPathStrictInterior (fun _=>c*d) inner).image ψ)
        (rawIntervalProtectedUnassignedList π d (fun e=>raw (Sum.inr e)) false true t Jret w):=by
  intro state e R targetRoot M hmatch assign hhub hsize hshort J S
  let hub:=fun a:LongRawSelectedOrdinary π d m ℓ e M=>(assign a).1
  let component:=fun a:LongRawSelectedOrdinary π d m ℓ e M=>(assign a).2
  let lens:=fun a:LongRawSelectedOrdinary π d m ℓ e M=>ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a).1
  have hinj:Function.Injective (fun a=>(⟨hub a,component a⟩:Σw,(F w).ConnectedComponent)):=by
    intro a b he
    apply assign.injective
    exact he
  have hsize':∀a,Fintype.card (component a)=lens a:=hsize
  have hshort':∀a,lens a<cutoff:=hshort
  obtain ⟨block,ext,inn,hext,hinner,hdis,paths,root,Cyc,hp,hlen,hsupp,hP,hcycle,hlenC,hdir,hcomp,hC,hcross⟩:=
    global_assignment_reserved_source_families F hF E hub component hinj lens hsize' w longComponents c d cutoff hlong hshort' hcapacity
  let finalInner:∀a:A,Fin (c*d+1)↪X:=fun a=>inn (.inl a)
  let select:J↪LongRawSelectedOrdinary π d m ℓ e M:=⟨Subtype.val,Subtype.val_injective⟩
  have hlength:∀j:J,ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M (select j)).1=(Cyc j).length:=by
    intro j
    exact (hlenC j).symm
  have hh:∀j:J,(longRawSelectedOrdinaryWheel π d m ℓ e M (select j)).val.2=w:=by
    intro j
    exact (hhub j.val).symm.trans j.property
  have hinner':∀a k,finalInner a k=ext (.inl a) ⟨k.val+2,by omega⟩:=fun a k=>hinner (.inl a) k
  obtain ⟨ψ,hψ,hpres,hrun,hOcc,hOldDir,hPhysical,hOldAvoid,hOldList⟩:=
    long_raw_packed_residual_embedding_with_protected_list (F w) (hF w) P₀ π c d m hc hd hcm hnoshort ℓ raw t Jret w index hindex
      (fun i=>ext i 0) (fun i=>ext i (Fin.last (c*d+4))) paths hp hP hlen ext hsupp hdis finalInner hinner'
      root Cyc hcycle hC hcross M hmatch select hlength hh
  let data:=actualResidualDataFromPacking (F w) (fun i=>ext i 0) (fun i=>ext i (Fin.last (c*d+4))) paths hp hP c d hc hd hlen
    _ _ _ _ m (3*d) π (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true) S w targetRoot
    root Cyc hcycle hC hcross
  have hold:ActualOldArcContainment data ψ (E w) (rawMixedPhysicalArc P₀ π d raw):=by
    intro pieces D hpair hvalid hArcs halign
    apply actual_old_arc_host_from_directed_images (F w) (hF w) (E w) pieces D hpair hvalid hArcs halign data ψ longComponents
      (fun i=>block i.val)
    · intro i
      change (paths i.val).support=List.ofFn (longReservedSigmaBlock (F w) longComponents c d (fun k=>E w (longComponents k)) (block i.val) d (le_refl _))
      rw [hsupp i.val,hext i.val]
    · intro j hj k hk
      exact hdir j k hk
    · exact hOldDir
  have holdPhysical:ActualOldArcContainment data ψ (E w)
      (fun x y=>({x,y}:Finset (Fin N))∈longRawPhysicalHubRims P₀ π d m ℓ raw true true M w):=by
    intro pieces D hpair hvalid hArcs halign
    refine actual_old_arc_host_from_directed_images (F w) (hF w) (E w) pieces D hpair hvalid hArcs halign data ψ longComponents
      (fun i=>block i.val) ?_ ?_ (fun x y=>({x,y}:Finset (Fin N))∈longRawPhysicalHubRims P₀ π d m ℓ raw true true M w) ?_
    · intro i
      change (paths i.val).support=List.ofFn (longReservedSigmaBlock (F w) longComponents c d (fun k=>E w (longComponents k)) (block i.val) d (le_refl _))
      rw [hsupp i.val,hext i.val]
    · intro j hj k hk
      exact hdir j k hk
    · exact hPhysical
  exact ⟨block,data,ext,finalInner,ψ,rfl,rfl,rfl,rfl,rfl,rfl,fun _=>rfl,hsupp,hext,hdis,hinner',hlenC,hdir,hψ,hpres,hOcc,hOldDir,hold,hPhysical,holdPhysical,hOldAvoid,hOldList⟩
end Oberwolfach
