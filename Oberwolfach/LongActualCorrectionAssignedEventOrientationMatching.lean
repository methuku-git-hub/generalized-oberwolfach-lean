module

public import Oberwolfach.LongActualCorrectionBeforeProtectedClassMatching
public import Oberwolfach.InducedFractionalCycles
public import Oberwolfach.LongActualFirstVortexProtectedOrientation
public import Oberwolfach.LongActualCorrectionProtectedOrientationMatching
public import Oberwolfach.LongActualCorrectionClassOrientationMatching
public import Oberwolfach.LongEarlyMatchingListsFromJointEvent
public import Oberwolfach.LongActualRawLawParameters
public import Oberwolfach.LongActualCorrectionJointEventOrientationMatching

@[expose] public section
/-! Use the correction first, then a protected class and its orientation,
and finally obtain matching and lists after one compatible deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance correctionAssignedEventFin (n:ℕ):DecidableEq (Fin n):=fun a b=>Classical.propDecidable (a=b)
theorem long_actual_correction_assigned_event_orientation_matching
    (α ρ₀ δ:ℝ) (d:ℕ) (hα:0<α) (hρ₀:0<ρ₀) (hδ:0<δ) (hd:2≤d):
    ∃c:ℝ,0<c ∧ ∀B:ℕ, ∃N:ℕ,1≤N ∧ ∀n:ℕ,N≤n→
    ∀ {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (P:SimpleGraph (Fin n)) (Dnat m:ℕ) (β εQ:ℝ)
    (Q:Vortex U P Dnat β εQ m) (π:Equiv.Perm (Fin n)) (r size a₀ b₀ e₀ f₀:ℕ)
    (εAbs ζ ξCorr ξClass:ℝ) (z:MarkedExpandedActualOutcome (U:=U) π d)
    (W:Finset U)
    (K:ℕ) (θ D alpha γ eps βList:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (ρ:ℝ),
    let V:=Fin n
    let ω:=z.1
    let σ:RawMarkedOutcome V U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (ω e)
    let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false)) z.2 false false
    let s:ℝ:=(1/100)/(((r+4):ℕ):ℝ)
    let a:=longAssignedApproxMarkedWeight F hF K (r+4) θ
    let b:=longAssignedApproxOrdinaryWeight F hF K (r+4) θ
    let p:=ρ*(1/100)/2
    let k:=ρ*s/2
    let p₂:=(∑u,b u)/D
    let k₂:=(∑u,a u)/D
    let u:=2*(∑w,(1-1/100-s-a w-b w))/D
    let Matching:=fun Del:SimpleGraph V=>LongEarlyMatchingListsForDeletion r K d θ D alpha γ eps Δ βList P π F hF weight w z (Q.extendedVertices 1) Del;
    (  let ni:=@longPaddedSeedExponent K
  let hni:=@long_padded_seed_exponent_positive K
  let Wm:=longAssignedMarkedSeed F hF K (r+4) d θ D π weight
  let Wo:=longAssignedOrdinarySeed F hF K (r+4) d θ D P π ni hni w
  let Wmix:=longMixedSeedWeight Wm Wo
  let ℓ:=fun i=>ni i+2
  let R:=longRawHubResources (U:=U) π d (r+4) ℓ;
    εQ≤βList/32→1/(100*((r+4:ℕ):ℝ))≤βList/16→
    ∀(Del:SimpleGraph (Fin n)),(∀x,(Del.degree x:ℝ)≤Δ*n)→
  (          let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
          let S:=longRawSurvivingResources P π d raw true true Del.edgeFinset
          let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
          let e:S↪LongRawHubResource n U:=Function.Embedding.subtype _
          let Cand:=RestrictedResource (mixedCandidateResources R) e
          let Q:=restrictedResourceSet (mixedCandidateResources R) e
          let fS:=survivingResourceEmbedding S T (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset)
          let φ:=fS.trans (markedRawSampledPhysicalEmbedding P π d raw true true)
          let hub:=longRawHubNames (U:=U) π d (r+4) ℓ
          let test:=fun (j:LongRetainedHubTest F hF K θ) (c:Cand)=>longRetainedHubIndicator F hF θ hub j c.val
          ∃M:Finset Cand,(∀c∈M,0<mixedCandidateWeight Wmix c.val) ∧
            (∀c∈M,∀c'∈M,c≠c'→Disjoint (Q c) (Q c')) ∧
            (∀x,alpha*n≤(rimIncidentResources φ x).card →
              ((rimIncidentResources φ x\M.biUnion Q).card:ℝ)≤γ*(rimIncidentResources φ x).card) ∧
            (∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (alpha*n) (γ*(longRawIncidenceSet S i).card)) ∧
            (∀i,alpha*n≤(longRawIncidenceSet S i).card →
              ((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤γ*(longRawIncidenceSet S i).card) ∧
            (∀j,(1-γ)*(∑c,test j c*mixedCandidateWeight Wmix c.val)≤∑c∈M,test j c) ∧
            (∀j,(∑c∈M,test j c)≤(1+γ)*(∑c,test j c*mixedCandidateWeight Wmix c.val)) ∧
            (∀x,((physicalRimResidualGraph (markedRawSampledPhysicalEmbedding P π d raw true true)
              ((M.map (survivingCandidateEmbedding (mixedCandidateResources R) S T
                (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset))).biUnion
                (restrictedResourceSet (mixedCandidateResources R) (Function.Embedding.subtype (·∈T))))).degree x:ℝ)≤max alpha γ*n+(Δ*n)) ∧
            let selected:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e)
            let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) false
              (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false false
            ∀(Reserve:Finset (Finset (Fin n)⊕(Fin n×U))) (X:Finset (Fin n)) (Z:Finset U),
            MarkedFixedTerminalAbsorber P π d (r+4) selected H Reserve X Z →
            let state:=longRawHubState P π d raw true true
    let T:=bernoulliVertexSet state
    let eraw:{z // z∈T}↪_:=Function.Embedding.subtype _
    let q:=survivingCandidateEmbedding (mixedCandidateResources R) S T (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset)
    let N:=M.map q
    let A:=LongRawSelectedOrdinary π d (r+4) ℓ eraw N
    let Q:=longRawSelectedOrdinaryWheel π d (r+4) ℓ eraw N
    ∃assign:A↪(Σu,(F u).ConnectedComponent),
    ∃C:∀a:A,(F (Q a).val.2).ConnectedComponent,
      (∀a,(⟨(Q a).val.2,C a⟩:Σu,(F u).ConnectedComponent)=assign a) ∧
    (∀u,Fintype.card (longRawSourceDomain F π d (r+4) ℓ eraw N C u) =
      ∑i:Fin K,(N.filter (fun c=>c.val.1=some i ∧
        longRawSeedHub π d (r+4) ℓ c.val.1 c.val.2=u)).card * ℓ i) ∧
    (∀u,Fintype.card {v:Fin n // v∉longRawSourceDomain F π d (r+4) ℓ eraw N C u} =
      n - ∑i:Fin K,(N.filter (fun c=>c.val.1=some i ∧
        longRawSeedHub π d (r+4) ℓ c.val.1 c.val.2=u)).card * ℓ i) ∧
    (∀u,|((Fintype.card (longRawSourceDomain F π d (r+4) ℓ eraw N C u):ℕ):ℝ) -
      (1-θ)*(n:ℝ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i u)| ≤
      ((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ))) ∧
    (∀u,|((Fintype.card {v:Fin n // v∉longRawSourceDomain F π d (r+4) ℓ eraw N C u}:ℕ):ℝ) -
      ((n:ℝ)-(1-θ)*(n:ℝ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i u))| ≤
      ((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ))) ∧
    (∀u, (n:ℝ)*ordinaryAssignedFraction F hF K u none -
      ((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ)) ≤
        ((Fintype.card {v:Fin n // v∉longRawSourceDomain F π d (r+4) ℓ eraw N C u}:ℕ):ℝ) ∧
      ((Fintype.card {v:Fin n // v∉longRawSourceDomain F π d (r+4) ℓ eraw N C u}:ℕ):ℝ) ≤
        (n:ℝ)*(ordinaryAssignedFraction F hF K u none+(101/100:ℝ)*θ) +
          ((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ))) ∧
    (∀u v,K<Fintype.card ((F u).connectedComponentMk v)→
      v∉longRawSourceDomain F π d (r+4) ℓ eraw N C u) ∧
    let T:=longRawSourceDomain F π d (r+4) ℓ eraw N C
    ∃ψ:∀u,(T u)↪Fin n,
      (∀u x y,(F u).Adj x.val y.val→
        rawMarkedPairRims P π d raw (Sum.inl (ψ u x,ψ u y)) ∨
        rawMarkedPairRims P π d raw (Sum.inl (ψ u y,ψ u x))) ∧
      (∀u v,u≠v→Disjoint
        (partialFactorPhysicalEdges (T u) ((F u).induce (T u)) (ψ u))
        (partialFactorPhysicalEdges (T v) ((F v).induce (T v)) (ψ v))) ∧
      (∀u x y,(F u).Adj x.val y.val→Sum.inl ({ψ u x,ψ u y}:Finset (Fin n))∉Reserve) ∧
      (∀u x y,(F u).Adj x.val y.val→s(ψ u x,ψ u y)∉Del.edgeFinset)) ∧ LongSampleReservedLists P π d z Del (Q.extendedVertices 1) (βList/2))→
    εQ≤βList/32→1/(100*((r+4:ℕ):ℝ))≤βList/16→
    MarkedProtectedAbsorbableCorrectionWithBounds P π d r size a₀ b₀ e₀ f₀ εAbs ζ ξCorr σ H (Q.extendedVertices 1) W →
    ζ+ξClass+δ≤Δ→
    0≤εQ→εQ≤((min α (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16)/32→
    ρ₀≤ρ→ρ≤1→0<D→0≤θ→θ≤1/100→3≤K→7≤r+4→
    (1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ→
    (∀u,factorPreparationClass (F u) K=none)→
    ρ*D=2*Fintype.card U→(Dnat:ℝ)=D→P.IsRegularOfDegree Dnat→
    (1/2+α)*(n:ℝ)≤D→
    0≤ξClass→ξClass≤min (min (c/4) (δ/16)) (α*(ρ₀/200)^2/4)→
    ((∀A:SimpleGraph (Fin n),(∀v,A.degree v≤B)→
        ∃S:SimpleGraph (Fin n),S≤P ∧ S.IsRegularOfDegree (2*Fintype.card U) ∧
          (∀x y,((spanningRestriction (⊤:SimpleGraph V) (Q.extendedVertices 1))⊔A).Adj x y→(S.Adj x y↔(longPhysicalStateGraph P (z.1) {0,1,2,3,4}).Adj x y)) ∧
          (∀v,((changed ((longPhysicalStateGraph P (z.1) {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n)) ∧
      (∀j v,|((∑w,sampledColourOrientation P (fun e=>z.1 (Sum.inl e)) j v w:ℕ):ℝ)-
        markedExpandedPhysicalProbability p k p₂ k₂ u j/2*P.degree v|<(n:ℝ)^(3/5:ℝ)) ∧
      (∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-(n:ℝ)^(3/4:ℝ)-2*(2*((3*d:ℕ):ℝ)+1)≤
        ((Finset.univ.filter (fun w=>
          0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) false x w ∧
          0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) false w y)).card:ℝ)))→
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2);
    ∃(DA:Finset (E⊕K)) (DS:Finset (V×U)),DS⊆S ∧
      (∀v,((DA.filter (fun a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a)).card:ℝ)≤
        8*(((r+4:ℕ):ℝ)+1)*ξCorr*Fintype.card V) ∧
      (∀v,((DS.filter (fun z=>v=z.1)).card:ℝ)≤4*(((r+4:ℕ):ℝ)+1)*ξCorr*Fintype.card V) ∧
      (∀u,((DS.filter (fun z=>u=z.2)).card:ℝ)≤4*(((r+4:ℕ):ℝ)+1)*ξCorr*Fintype.card V) ∧
      (DA.card:ℝ)≤8*(((r+4:ℕ):ℝ)+1)*ξCorr*(Fintype.card V:ℝ)^2 ∧
      (DS.card:ℝ)≤4*(((r+4:ℕ):ℝ)+1)*ξCorr*(Fintype.card V:ℝ)^2 ∧
      (markedFiniteResources tail head ktail khead π DA DS).filter (markedInnerResource (Q.extendedVertices 1) W)=∅ ∧
      (∀v,((markedSampleArcSetGraph P π d σ DA).degree v:ℝ)≤ζ*Fintype.card V) ∧
      (∀z,((markedFiniteSpokeGraph DS).degree z:ℝ)≤ζ*Fintype.card V) ∧
      (∀x∈(Q.extendedVertices 1),∀y∈(Q.extendedVertices 1),¬(markedSampleArcSetGraph P π d σ DA).Adj x y) ∧
      (∀x∈(Q.extendedVertices 1),∀u∈W,¬(markedFiniteSpokeGraph DS).Adj (Sum.inl x) (Sum.inr u)) ∧
      (∀Protected:SimpleGraph V,(∀x y,Protected.Adj x y→x∈(Q.extendedVertices 1) ∧ y∈(Q.extendedVertices 1))→
        ∀x y,(markedSampleArcSetGraph P π d σ DA).Adj x y→¬Protected.Adj x y) ∧
    let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ DA).edgeFinset
    let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph DS)
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
    MarkedRemainderDivisible (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ
      (Finset.univ.filter (fun z:V×U=>H' false z.1 z.2∨H' true z.1 z.2)) (r+4) ∧
    MarkedReservedTerminalAbsorberProperty (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' false) (H' true) π (3*d) r size a₀ b₀ e₀ f₀ εAbs ∧
    ∀A:SimpleGraph V,(∀v,A.degree v≤B)→
      (∀x y,(markedSampleArcSetGraph P π d σ DA).Adj x y→¬A.Adj x y)→
      ∃S:SimpleGraph V,S≤P ∧ S.IsRegularOfDegree (2*Fintype.card U) ∧
        (∀x y,((spanningRestriction (⊤:SimpleGraph V) (Q.extendedVertices 1))⊔A).Adj x y→
          (S.Adj x y↔(longPhysicalStateGraph P ω {0,1,2,3,4}).Adj x y)) ∧
        (∀v,((changed ((longPhysicalStateGraph P ω {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n) ∧
        ∃M:V→V→ℕ,(∀x y,M x y+M y x=if S.Adj x y then 1 else 0) ∧
          (∀v,(∑w,M v w)=Fintype.card U ∧ (∑w,M w v)=Fintype.card U) ∧
          (∀v,((orientationDisagreementGraph (longPhysicalStateGraph P ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) M).degree v:ℝ)≤δ*n) ∧
          (∀x y,(orientationDisagreementGraph (longPhysicalStateGraph P ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) M).Adj x y→¬((spanningRestriction (⊤:SimpleGraph V) (Q.extendedVertices 1))⊔A).Adj x y) ∧
        ∀Kbad:SimpleGraph V,Kbad≤S→
          ∃Del:SimpleGraph V,(markedSampleArcSetGraph P π d σ DA)≤Del ∧
            ((longPhysicalStateGraph P ω {0,1,2,3,4})\S)≤Del ∧
            orientationDisagreementGraph (longPhysicalStateGraph P ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) M≤Del ∧
            (∀v,(Del.degree v:ℝ)≤Δ*n) ∧
            (∀x y,Del.Adj x y→¬((spanningRestriction (⊤:SimpleGraph V) (Q.extendedVertices 1))⊔A).Adj x y) ∧
            (∀x y,rawSelectedPhysicalRelation P π d (fun e=>ω (Sum.inl e)) x y→¬Del.Adj x y→M x y=1) ∧
            (∀x y,Kbad.Adj x y→M x y=1 ∨ M y x=1) ∧ (∀x y,M x y=1→P.Adj x y) ∧
            (∀x y,rawMixedPhysicalArc P π d (fun e=>rawExpandedApproximateCollapse e (ω e)) x y→¬Del.Adj x y→M x y=1) ∧ Matching Del := by
  obtain ⟨c,hc,hMain⟩:=long_actual_correction_joint_event_orientation_matching α ρ₀ δ d hα hρ₀ hδ
  refine ⟨c,hc,?_⟩
  intro B
  obtain ⟨N,hN,hMain⟩:=hMain B
  refine ⟨N,hN,?_⟩
  intro n hn U _ _ _ Δ P Dnat m β εQ Q π r size a₀ b₀ e₀ f₀ εAbs ζ ξCorr ξClass z W K θ D alpha γ eps βList F hF Allowed hAllowed weight w ρ
  dsimp only
  intro hJoint hεcap htrim hCorr hsum hεQ hcap hρlo hρhi hD hθ0 hθ hK hm hcut hclass hsize hDnat hreg hmin hξ hξhi hsample
  have hLaw:=long_assigned_actual_raw_law_parameters (by omega) F hF Allowed hAllowed K (by omega) (r+4) d hm hd θ ρ₀ ρ D
    hθ0 hθ hρ₀ hρlo hρhi hD hsize hcut hclass
  dsimp only at hLaw
  have hdegree : ∀v, |(P.degree v:ℝ)-D|≤(0:ℝ)*n := by
    intro v
    rw [hreg v,hDnat]
    simp
  have hmin' : ∀v,(1/2+α)*(n:ℝ)≤P.degree v := by
    intro v
    rw [hreg v,hDnat]
    exact hmin
  exact hMain n hn Δ P Dnat m β εQ Q π r size a₀ b₀ e₀ f₀ εAbs ζ ξCorr ξClass z W K θ D alpha γ eps βList F hF weight w
    ρ ((1/100)/(((r+4):ℕ):ℝ)) 0 (longAssignedApproxMarkedWeight F hF K (r+4) θ)
    (longAssignedApproxOrdinaryWeight F hF K (r+4) θ)
    hJoint hεcap htrim hCorr hsum hεQ hcap hρlo hρhi hD hLaw.2.1 hLaw.2.2.1 hLaw.2.2.2.1 hLaw.2.2.2.2.1
    (le_refl _) (by linarith) hsize hdegree hmin' hξ hξhi hsample
end Oberwolfach
