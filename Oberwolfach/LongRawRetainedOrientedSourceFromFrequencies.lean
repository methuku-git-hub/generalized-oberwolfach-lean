module

public import Oberwolfach.LongRawSurvivingAlignedAllRimsRetained
public import Oberwolfach.LongRawSurvivingAlignedProtection
public import Oberwolfach.LongRawSurvivingAlignedSource
public import Oberwolfach.LongPaddedSurvivingSourceMatchingMaps
public import Oberwolfach.LongAssignedClassReservation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawSurvivingRetainedOrientedFrequencyFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_raw_surviving_retained_oriented_source_from_frequencies
    {N K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin N)]
    (F:U→SimpleGraph (Fin N)) (hF:∀w,(F w).IsRegularOfDegree 2) (hU:0<Fintype.card U)
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
      (N:ℝ)*longAssignedIntervalProbability F hF K m θ w g/d|<(N:ℝ)^(3/4:ℝ)/d)
    (σ:∀e:RawWheelCoordinate (Fin N) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (hraw:raw=(fun e=>rawExpandedApproximateCollapse e (σ e)))
    (Del:Finset (Sym2 (Fin N))) (Dens:ℝ)
    (w:∀i:Fin K,OrdinaryCycle P₀ (longPaddedSeedExponent i+2)→ℝ)
    (wM:MarkedWheel (Prod.fst:Fin N×Fin N→Fin N) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (Reserve:Finset (Finset (Fin N)⊕(Fin N×U))) (X:Finset (Fin N)) (Z:Finset U)
    (eps lam:ℝ) (hlam:0≤lam) (hlamθ:lam≤θ)
    (heps:eps≤lam*(θ/(100*(K:ℝ)^2))):
    letI:Nonempty U:=Fintype.card_pos_iff.mp hU
    let selected:RawMarkedOutcome (Fin N) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (σ e)
    let H:=retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false false
    MarkedFixedTerminalAbsorber P₀ π d m selected H Reserve X Z→
      ∃(Dsrc:∀w,Fin N→Fin N→Prop) (orig:∀w,List (PrescribedSourcePiece (Fin N))),
      (∀w,(orig w).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset)) ∧
      (∀w p,p∈orig w→∃a xs,p=.cycle a xs ∧ p.OriginalValid (Dsrc w)) ∧
      (∀w,sourcePieceVerticesUnion (orig w)=Finset.univ ∧ sourcePieceEdgesUnion (orig w)=(F w).edgeFinset) ∧
      (∀w x y,Dsrc w x y↔(x,y)∈sourcePieceArcsUnion (orig w)) ∧
      ∃E:∀w (C:(F w).ConnectedComponent),SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph,
        (∀w x,Dsrc w x (factorCycleOrientation (F w) (E w) x)) ∧
        LateComplementContinuation (V:=Fin N) F Dsrc ∧
    let ℓ:=fun i:Fin K=>longPaddedSeedExponent i+2
    let state:=longRawHubState P₀ π d raw true true
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    let T:=bernoulliVertexSet state
    let S:=longRawSurvivingResources P₀ π d raw true true Del
    let q:=survivingCandidateEmbedding (mixedCandidateResources R) S T (long_raw_surviving_resources_subset P₀ π d raw true true Del)
    let eS:{z // z∈S}↪_:=Function.Embedding.subtype _
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) eS),
    (∀x∈M,∀y∈M,x≠y→Disjoint (restrictedResourceSet (mixedCandidateResources R) eS x)
      (restrictedResourceSet (mixedCandidateResources R) eS y))→
    let wO:=longAssignedOrdinarySeed F hF K m d θ Dens P₀ π (@longPaddedSeedExponent K) (@long_padded_seed_exponent_positive K) w
    let wmix:=longMixedSeedWeight wM wO
    (∀c∈M,0<mixedCandidateWeight wmix c.val)→
    (∀(u:U) (i:Fin K),θ/(100*(K:ℝ))≤longAssignedKeptFraction F hF K θ i u→
      let target:=longAssignedKeptFraction F hF K θ i u*(N:ℝ)/((longPaddedSeedExponent i+2:ℕ):ℝ)
      |(((M.filter (fun c=>c.val.1=some i ∧ longRawSeedHub π d m ℓ c.val.1 c.val.2=u)).card:ℝ)-(1-θ)*target)|≤eps*N)→

    ∃(ext:∀w:U,(retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w ⊕
        {a:Fin N // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) a true})→Fin ((m+1)*d+5)↪Fin N)
      (inner:∀w:U,retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w→Fin ((m+1)*d+1)↪Fin N)
      (ψ:∀w:U,Fin N→Fin N) ,
    ∃assign:LongRawSelectedOrdinary π d m ℓ e (M.map q)↪(Σw,(F w).ConnectedComponent),
    ∃(data:∀w:U,ActualResidualData
      (K:=(retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w) ⊕
        {a:Fin N // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) a true})
      (J:={a:LongRawSelectedOrdinary π d m ℓ e (M.map q) // (assign a).1=w}) (F w)) ,
    (∀w,(data w).c=m+1 ∧ (data w).d=d ∧ (data w).s₁=firstSumIndices ∧
      (data w).Cembed=(data w).t.biUnion (fun j=>((data w).C j).support.toFinset) ∧
      (∀i,((data w).P i).support=List.ofFn (ext w i)) ∧
      (∀a k,inner w a k=ext w (.inl a) ⟨k.val+2,by omega⟩) ∧
      (∀i (j:Fin (d+1)),bufferedMarker (m+1) d (ext w i) j∈(data w).prescribed→
        ψ w (bufferedMarker (m+1) d (ext w i) j)=(π^j.val)
          (retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true t Jret w i)) ∧
      (∀i∈(data w).s₂,∀j:Fin (d+1),∃x∈(data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w),
        ψ w x=(π^j.val) (retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true t Jret w i)) ∧
      Disjoint (bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)) (data w).remaining ∧
      Set.InjOn (ψ w) (↑((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)):Set (Fin N)) ∧
      ActualOldArcContainment (data w) (ψ w) (E w)
        (fun x y=>({x,y}:Finset (Fin N))∈longRawPhysicalHubRims P₀ π d m ℓ raw true true (M.map q) w) ∧
      Disjoint (((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)).image (ψ w))
        (Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false false false v w)) ∧
      (data w).s₂=secondSumIndices ∧ (data w).t=Finset.univ ∧
      (∀i,(data w).T i=packedPhysicalSpokePositions _ _ _ _ m (3*d) d π
        (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true)
        (longRawMarkedWheelsAtHub P₀ π d m ℓ raw true true (M.map q) w) w
        (retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true t Jret w i)) ∧
      (∀j,((data w).C j).length=ℓ (longRawSelectedOrdinaryPayload π d m ℓ e (M.map q) j.val).1) ∧
      (∀j,((data w).C j).toSubgraph.verts=
        (assignedComponentAtHub F (fun a=>(assign a).1) (fun a=>(assign a).2) w j).supp) ∧
      (∀j:{a:LongRawSelectedOrdinary π d m ℓ e (M.map q) // (assign a).1=w},∀x∈Finset.univ.image ((longRawSelectedOrdinaryWheel π d m ℓ e (M.map q) j.val).val.1.val),
        x∈((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)).image (ψ w)) ∧
      (∀W∈longRawMarkedWheelsAtHub P₀ π d m ℓ raw true true (M.map q) w,∀i:Fin (m+1),
        W.1.val i∈((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)).image (ψ w)) ∧
      ActualWheelRimsFamilyOld (data w) (ψ w) _ _ _ _ m (3*d) π _ _ (longRawMarkedWheelsAtHub P₀ π d m ℓ raw true true (M.map q) w) ∧
      ActualAssignedOrdinaryRimsOld (data w) (ψ w)
        (fun j:{a:LongRawSelectedOrdinary π d m ℓ e (M.map q) // (assign a).1=w}=>ℓ (longRawSelectedOrdinaryPayload π d m ℓ e (M.map q) j.val).1)
        (fun j=>(longRawSelectedOrdinaryWheel π d m ℓ e (M.map q) j.val).val.1.val) ∧
      (∀i j,i≠j→Disjoint (Finset.univ.image (ext w i)) (Finset.univ.image (ext w j))) ∧
      (∀x,x∈(data w).oldDomain→x∉bufferedPathFullDomain (fun _=>(m+1)*d) (inner w)→
        ψ w x∉markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w=>d) Subtype.val) ∧
      (∀i (j:Fin ((m+1)*d+4)),factorCycleOrientation (F w) (E w) (ext w i j.castSucc)=ext w i j.succ) ∧
      ActualOldArcContainment (data w) (ψ w) (E w) (rawMixedPhysicalArc P₀ π d raw)) ∧
    ∃(pieces:∀w,List (PrescribedSourcePiece {x // x∈(data w).remaining})),
      (∀w,prescribedDependentGraph pieces w=((data w).graph).induce (↑(data w).remaining:Set (Fin N))) ∧
      (∀w x y,prescribedDependentDigraph pieces w x y ↔ Dsrc w x.1 y.1 ∧ (data w).graph.Adj x.1 y.1) ∧
    let old:=fun w=>((data w).deletedEdges\(Finset.univ.biUnion
      (fun i:{i // i∈(data w).s₁}=>((data w).path (.inl i)).edges.toFinset))).image (Sym2.map (ψ w))
    ∃Pack:Finset (Sym2 (Fin N)),
      (∀w z,w≠z→Disjoint (old w) (old z)) ∧ (∀w,old w⊆Pack) ∧
      Pack⊆(longApproximatePhysicalGraph P₀ π d σ).edgeFinset ∧
      (∀x y,rawSelectedPhysicalRelation P₀ π d (fun e=>σ (Sum.inl e)) x y→s(x,y)∉Pack) ∧
      Pack=Finset.univ.biUnion old ∧
      Pack=(physicalRimCandidateUnion (markedRawSampledPhysicalEmbedding P₀ π d raw true true)
        (restrictedResourceSet (mixedCandidateResources R) e) (M.map q)).edgeFinset ∧

      (∀a,(assign a).1=(longRawSelectedOrdinaryWheel π d m ℓ e (M.map q) a).val.2) ∧
      (∀a,Fintype.card (assign a).2=ℓ (longRawSelectedOrdinaryPayload π d m ℓ e (M.map q) a).1) :=by
  subst raw
  intro selected H habs
  letI:Nonempty U:=Fintype.card_pos_iff.mp hU
  let raw:RawMarkedOutcome (Fin N) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
  obtain ⟨Dsrc,orig,hpair,hcycles,hwhole,hArcs,E,halign,hres,hfamily⟩:=
    long_raw_surviving_aligned_all_rims_retained_packing F hF hU Allowed hAllowed hn hK hclass P₀ π d m hd hm hnoshort θ hθ hcut hlarge raw t Jret hcounts σ rfl Del
  have hlen : (fun i:Fin K=>longPaddedSeedExponent i+2)=longAssignedPaddedLength :=by
    funext i
    exact long_padded_seed_length_eq_exponent i
  rw [← hlen] at hfamily
  refine ⟨Dsrc,orig,hpair,hcycles,hwhole,hArcs,E,halign,hres,?_⟩
  intro ℓ state e R T S q eS M hmatch wO wmix hpos herr
  have hlong:=long_class_assigned_frequency hn F hF Allowed hAllowed K (by omega) hclass
  have hmaps:=long_padded_surviving_source_matching_and_component_maps hn (by omega : 0<K) hK F hF m d θ Dens hθ P₀ π hlong w wM σ t Jret Reserve X Z Del eps lam hlam hlamθ heps habs M hpos hmatch herr
  obtain ⟨assign,data,ext,inner,ψ,hprops,hrest⟩:=hfamily M hmatch hmaps.2.2
  exact ⟨ext,inner,ψ,assign,data,hprops,hrest⟩
end Oberwolfach
