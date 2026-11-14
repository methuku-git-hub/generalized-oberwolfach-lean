module

public import Oberwolfach.LongAssignedVortexManuscriptMatchingPartials
public import Oberwolfach.MarkedVortexPreselectFromJointSample
public import Oberwolfach.LongAssignedVortexReferenceProbabilitySeparate
public import Oberwolfach.LongAssignedReferenceMatchingPartials

@[expose] public section
/-! The actual fixed-vortex reference and absorber event is intersected with
one assigned matching outcome, retaining its ordinary partial-factor maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_assigned_vortex_reference_manuscript_matching_and_selected_absorber
    (r h k₀ Qpow:ℕ) (hr:2≤r) (hm:7≤r+4) (hlen:r+4+1=(k₀+2)*2)
    (αRef ρ₀ sstar tstar kstar tol χActive Qexp pstarRef ζActive:ℝ)
    (hQpow:0<Qpow) (hQexp:0<Qexp) (hαRef:0<αRef) (hαRef1:αRef≤1) (hρ₀:0<ρ₀)
    (hsstar:0<sstar) (hsstar1:sstar≤1/100) (htstar:0<tstar) (htstar1:tstar≤1)
    (horder:tstar≤sstar) (hkstar:0<kstar)
    (hmargin:successorCycleRatio k₀+αRef/2≤1/2+αRef)
    (htol:0<tol) (hχActive:0<χActive) (hpstarRef:0<pstarRef)
    (hpstarBound:pstarRef≤ρ₀*tstar/4) (hζActive:0<ζActive):
    ∃ εAbs ζAbs δAbs:ℝ,0<εAbs ∧ 0<ζAbs ∧ 0<δAbs ∧
    ∃ βconfig:ℝ,0<βconfig ∧ ∀ εref δref χ β ε:ℝ,
    0<εref→0<δref→0<χ→0≤β→β≤αRef/8→β≤1/4→β≤εref/4→0<ε→ε<1/4→
    ∀ ε₀:ℝ,ε₀<1→χ+2*χActive<ε₀→∀ d:ℕ,∀ hd:2≤d,∃ m₀:ℕ,1≤m₀ ∧
    ∀ size:ℕ,∃ a₀ b₀ e₀:ℕ,∀ f₀:ℕ,∃ n₀:ℕ,1≤n₀ ∧
    ∀ (K:ℕ) (hK3:3≤K) (θ BM:ℝ) (hθpos:0<θ) (hθ:θ≤1/100) (hBM:0<BM)
      (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
      (alpha γ eps lam:ℝ) (heps:0<eps) (heps1:eps≤1) (hγε:γ≤eps) (hlam:0≤lam)
      (hlamθ:lam≤θ) (hepsAssign:3*eps≤lam*(θ/(100*(K:ℝ)^2)))
      (halpha:0<alpha) (halphaMass:alpha≤θ/(200*(K:ℝ)*(K:ℝ))) (hγ:0<γ),
    let m:=r+4
    let ni:=@longPaddedSeedExponent K
    let hni:=@long_padded_seed_exponent_positive K
    ∃η:ℝ,0<η ∧ ∃t₀ τ₀ Δ ξ:ℝ,0<t₀ ∧ 0<τ₀ ∧ τ₀≤1/16 ∧ 0<Δ ∧ 0<ξ ∧ 4*ξ≤eps/2 ∧
    ∃N:ℕ,∀n:ℕ,∀hn:max N 1≤n,∀(U:Type) [Fintype U] [DecidableEq U],
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (P:SimpleGraph (Fin n)) (Dnat vsize:ℕ) (hreg:P.IsRegularOfDegree Dnat) (hDnat:0<Dnat)
    (hmind:(1/2+αRef)*n≤(Dnat:ℝ))
    (hrlo:ρ₀≤ initialIndexDensity U Dnat) (hrhi:initialIndexDensity U Dnat≤1)
    (hcut:(1/((m:ℝ)+1))/(d:ℝ)≤θ) (hclass:∀u,factorPreparationClass (F u) K=none)
    (hmV:m₀≤vsize) (hvN:vsize≤n) (Q:Vortex U P Dnat β ε vsize) (π:Equiv.Perm (Fin n))
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x) (L:ℕ) (hL:L<Q.length)
    (τ A:ℝ) (weight:(Fin (m+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) (Dnat:ℝ) τ A BM weight)
    (hDlo:(n:ℝ)/2≤(Dnat:ℝ)) (hDhi:(Dnat:ℝ)≤2*n)
    (w:∀i,OrdinaryCycle P (ni i+2)→ℝ) (hw0:∀i C,0≤w i C)
    (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(ni i)) (huv:Fintype.card U≤n)
    (εHost:ℝ) (hεHost:0≤εHost)
    (he:∀i∈longRetainedSeedIndices F hF K θ,∀x y,
      (∑C:OrdinaryCycle P (ni i+2),if C.val.val.Adj x y then w i C else 0)=if P.Adj x y then 1 else 0)
    (hbudgetV:∀i∈longRetainedSeedIndices F hF K θ,
      6*((ni i+2:ℕ):ℝ)^4*BO i*(2*(3*d))+εHost*n≤τ*(Dnat:ℝ))
    (hbudgetE:∀i∈longRetainedSeedIndices F hF K θ,
      5*((ni i+2:ℕ):ℝ)^4*BO i*(2*(3*d))/n≤τ)
    (hτnonneg:0≤τ) (hτbound:τ≤τ₀)
    (hLterminal:L+1=Q.length) (hεAbs:ε≤εAbs) (hAbsSize:2*vsize≤size)
    (F₀:Finset (Finset (Fin n)⊕(Fin n×U))) (hF₀:F₀.card≤f₀),
    let ρ:=initialIndexDensity U Dnat
    let D:ℝ:=Dnat
    let hsize:ρ*D=2*Fintype.card U:=by dsimp [ρ,D,initialIndexDensity];field_simp
    let t:=t₀
    let tHub:=ξ*(n:ℝ)
    let b:=longAssignedApproxOrdinaryWeight F hF K m θ
    let a:=longAssignedApproxMarkedWeight F hF K m θ
    let p₁:=ρ*(1/100)/2
    let k₁:=ρ*((1/100)/(m:ℝ))/2
    let p₂:=(∑u,b u)/D
    let k₂:=(∑u,a u)/D
    let udens:=2*(∑u,(1-1/100-(1/100)/(m:ℝ)-a u-b u))/D
    let q:=longAssignedIntervalProbability F hF K m θ
    let s:=longAssignedSpokeProbability F hF K m θ
    let hLaw:=long_assigned_actual_raw_law_parameters (by omega) F hF Allowed hAllowed K (by omega) m d hm hd θ ρ₀ ρ D
      hθpos.le hθ hρ₀ hrlo hrhi (by dsimp [D];exact_mod_cast hDnat) hsize hcut hclass
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p₁ k₁ p₂ k₂ udens
      hLaw.1 hLaw.2.1 hLaw.2.2.1 hLaw.2.2.2.1 hLaw.2.2.2.2.1 hLaw.2.2.2.2.2.1
      d hd q hLaw.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.1 s
      hLaw.2.2.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.2.2)
    let f:=fun (ω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e) e=>
      rawExpandedMarkedCollapse e (ω e)
    let pstar:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*((m:ℝ)+1))))
    let BMseed:=2*BM/pstar^(2*m+1)
    let BOseed:=fun i=>2*BO i/pstar^(2*(ni i+2))
    let Wm:=longAssignedMarkedSeed F hF K m d θ D π weight
    let Wo:=longAssignedOrdinarySeed F hF K m d θ D P π ni hni w
    let C:=10*(((m:ℝ)+1)^4*BMseed+∑i:Fin K,((ni i:ℝ)+2)^4*BOseed i)
    let ℓ:=fun i=>ni i+2
    let W:=longMixedSeedWeight Wm Wo
    let R:=longRawHubResources (U:=U) π d m ℓ
    let Pair:Option (Fin K)→ℝ:=fun i=>match i with
      | none=>((m:ℝ)+1)^4*BMseed
      | some i=>((ni i:ℝ)+2)^3*BOseed i
    let Kpair:=1+((m:ℝ)+1)^4*BMseed+∑i:Fin K,((ni i:ℝ)+2)^3*BOseed i
    let failure:=4*(Fintype.card U:ℝ)*Real.exp (-2*tHub^2/((4*(d:ℝ)+3)^2*(n:ℝ)))
    letI : Nonempty (Fin n):=⟨⟨0,by omega⟩⟩
    let Ret:=fun raw:RawMarkedOutcome (Fin n) U Bool Bool=>
      StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
        (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false))
    let ν:=fun raw:RawMarkedOutcome (Fin n) U Bool Bool=>
      startRetentionLaw (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
        (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)) (startRetentionMinimum_le _)
    ∀ (hpRef:kstar≤p₁) (hkRef:kstar≤k₁) (htRef:tstar≤(1/100:ℝ)/(m:ℝ)),
    let Eref:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Bool) π d false=>
      MarkedReferenceActiveAbsorberProperty r h d αRef βconfig εref δref tol ζActive ζAbs tstar εAbs
        size a₀ b₀ e₀ f₀ P Dnat vsize β ε Q π hpres L (1/100) p₁ k₁ q s false false z
    ∃z:(Σω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,Ret (f ω)),
      0<(μ.sigma (fun ω=>ν (f ω))).mass z ∧ Eref ⟨f z.1,z.2⟩ ∧
      (let σ:=f z.1
       let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) false
         (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false)) z.2 false false
       let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
       let KArc:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
       ∃ C:MarkedSupportedEdgeSet (fun e:E=>e.val.1) (fun e=>e.val.2)
           (fun e:KArc=>e.val.1) (fun e=>e.val.2) π U,
         Disjoint C.edges F₀ ∧ C.edges.card≤e₀ ∧ C.rows.card≤a₀ ∧ C.hubs.card≤b₀ ∧
         C.edges.filter (markedInnerResource (Q.extendedVertices 1) (Q.extendedIndices 1))=∅ ∧
         MarkedFixedTerminalAbsorber P π d m σ H C.edges
           (Q.extendedVertices (L+1)) (Q.extendedIndices (L+1))) ∧
        (∀b u,|rawMarkedRestrictedSpokeCol π d (fun e=>z.1 (Sum.inr e)) true true b u Finset.univ-
          (if b then q u true else s u true)*(n:ℝ)|<tHub) ∧
        (∀u,|(((ordinaryCommonHubSpokeRoots u).filter (fun root=>
          longRawHubState P π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) true true root=true)).card:ℝ)-
          longAssignedApproxOrdinaryWeight F hF K m θ u*n|≤tHub) ∧
        rawMarkedSeedConcentrated P π d m p₂ k₂ q s true true t Wm
          (fun e=>rawExpandedApproximateCollapse e (z.1 e)) ∧
        (∀i,rawOrdinarySeedConcentrated P π d (ni i+2) p₂ k₂ q s true true t (Wo i)
          (fun e=>rawExpandedApproximateCollapse e (z.1 e))) ∧
        (∀i root,longRawHubState P π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) true true root=true→
          |resourcePatternLoad (longRawHubResources (U:=U) π d m (fun i=>ni i+2) i)
            (longMixedSeedWeight Wm Wo i) (fun _ _=>true) root
            (longRawHubState P π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) true true)-
            longAssignedMixedTarget F hF K m θ D p₂ k₂ i root|≤
          t+τ*longAssignedMixedTarget F hF K m θ D p₂ k₂ i root) ∧
        (∀(Del:SimpleGraph (Fin n)) (δ:ℝ), (∀x,(Del.degree x:ℝ)≤δ)→
          δ≤Δ*n→
          let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
          let hub:=longRawHubNames (U:=U) π d m ℓ
          let S:=longRawSurvivingResources P π d raw true true Del.edgeFinset
          let e:{v // v∈S}↪_:=Function.Embedding.subtype _
          ∀ztest:LongRetainedHubTest F hF K θ,
            θ*(n:ℝ)/(200*(K:ℝ)*(K:ℝ))≤
              ∑c:RestrictedResource (mixedCandidateResources R) e,
                longRetainedHubIndicator F hF θ hub ztest c.val*mixedCandidateWeight W c.val) ∧
        (∀(Del:SimpleGraph (Fin n)) (δ:ℝ), (∀x,(Del.degree x:ℝ)≤δ)→
          δ≤Δ*n→0≤t+C*(δ/(n:ℝ))+4*τ ∧ t+C*(δ/(n:ℝ))+4*τ≤eps/2) ∧
        (∀(Del:SimpleGraph (Fin n)) (δ:ℝ), (∀x,(Del.degree x:ℝ)≤δ)→
          δ≤Δ*n→
          let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
          let S:=longRawSurvivingResources P π d raw true true Del.edgeFinset
          let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
          let e:S↪LongRawHubResource n U:=Function.Embedding.subtype _
          let Cand:=RestrictedResource (mixedCandidateResources R) e
          let Q:=restrictedResourceSet (mixedCandidateResources R) e
          let fS:=survivingResourceEmbedding S T (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset)
          let φ:=fS.trans (markedRawSampledPhysicalEmbedding P π d raw true true)
          let hub:=longRawHubNames (U:=U) π d m ℓ
          let test:=fun (j:LongRetainedHubTest F hF K θ) (c:Cand)=>longRetainedHubIndicator F hF θ hub j c.val
          ∃M:Finset Cand,(∀c∈M,0<mixedCandidateWeight W c.val) ∧
            (∀c∈M,∀c'∈M,c≠c'→Disjoint (Q c) (Q c')) ∧
            (∀x,alpha*n≤(rimIncidentResources φ x).card →
              ((rimIncidentResources φ x\M.biUnion Q).card:ℝ)≤γ*(rimIncidentResources φ x).card) ∧
            (∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (alpha*n) (γ*(longRawIncidenceSet S i).card)) ∧
            (∀i,alpha*n≤(longRawIncidenceSet S i).card →
              ((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤γ*(longRawIncidenceSet S i).card) ∧
            (∀j,(1-γ)*(∑c,test j c*mixedCandidateWeight W c.val)≤∑c∈M,test j c) ∧
            (∀j,(∑c∈M,test j c)≤(1+γ)*(∑c,test j c*mixedCandidateWeight W c.val)) ∧
            (∀x,((physicalRimResidualGraph (markedRawSampledPhysicalEmbedding P π d raw true true)
              ((M.map (survivingCandidateEmbedding (mixedCandidateResources R) S T
                (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset))).biUnion
                (restrictedResourceSet (mixedCandidateResources R) (Function.Embedding.subtype (·∈T))))).degree x:ℝ)≤max alpha γ*n+δ) ∧
            let selected:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e)
            let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) false
              (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false false
            ∀(Reserve:Finset (Finset (Fin n)⊕(Fin n×U))) (X:Finset (Fin n)) (Z:Finset U),
            MarkedFixedTerminalAbsorber P π d m selected H Reserve X Z →
            let state:=longRawHubState P π d raw true true
    let T:=bernoulliVertexSet state
    let eraw:{z // z∈T}↪_:=Function.Embedding.subtype _
    let q:=survivingCandidateEmbedding (mixedCandidateResources R) S T (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset)
    let N:=M.map q
    let A:=LongRawSelectedOrdinary π d m ℓ eraw N
    let Q:=longRawSelectedOrdinaryWheel π d m ℓ eraw N
    ∃assign:A↪(Σu,(F u).ConnectedComponent),
    ∃C:∀a:A,(F (Q a).val.2).ConnectedComponent,
      (∀a,(⟨(Q a).val.2,C a⟩:Σu,(F u).ConnectedComponent)=assign a) ∧
    (∀u,Fintype.card (longRawSourceDomain F π d m ℓ eraw N C u) =
      ∑i:Fin K,(N.filter (fun c=>c.val.1=some i ∧
        longRawSeedHub π d m ℓ c.val.1 c.val.2=u)).card * ℓ i) ∧
    (∀u,Fintype.card {v:Fin n // v∉longRawSourceDomain F π d m ℓ eraw N C u} =
      n - ∑i:Fin K,(N.filter (fun c=>c.val.1=some i ∧
        longRawSeedHub π d m ℓ c.val.1 c.val.2=u)).card * ℓ i) ∧
    (∀u,|((Fintype.card (longRawSourceDomain F π d m ℓ eraw N C u):ℕ):ℝ) -
      (1-θ)*(n:ℝ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i u)| ≤
      ((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ))) ∧
    (∀u,|((Fintype.card {v:Fin n // v∉longRawSourceDomain F π d m ℓ eraw N C u}:ℕ):ℝ) -
      ((n:ℝ)-(1-θ)*(n:ℝ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i u))| ≤
      ((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ))) ∧
    (∀u, (n:ℝ)*ordinaryAssignedFraction F hF K u none -
      ((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ)) ≤
        ((Fintype.card {v:Fin n // v∉longRawSourceDomain F π d m ℓ eraw N C u}:ℕ):ℝ) ∧
      ((Fintype.card {v:Fin n // v∉longRawSourceDomain F π d m ℓ eraw N C u}:ℕ):ℝ) ≤
        (n:ℝ)*(ordinaryAssignedFraction F hF K u none+(101/100:ℝ)*θ) +
          ((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ))) ∧
    (∀u v,K<Fintype.card ((F u).connectedComponentMk v)→
      v∉longRawSourceDomain F π d m ℓ eraw N C u) ∧
    let T:=longRawSourceDomain F π d m ℓ eraw N C
    ∃ψ:∀u,(T u)↪Fin n,
      (∀u x y,(F u).Adj x.val y.val→
        rawMarkedPairRims P π d raw (Sum.inl (ψ u x,ψ u y)) ∨
        rawMarkedPairRims P π d raw (Sum.inl (ψ u y,ψ u x))) ∧
      (∀u v,u≠v→Disjoint
        (partialFactorPhysicalEdges (T u) ((F u).induce (T u)) (ψ u))
        (partialFactorPhysicalEdges (T v) ((F v).induce (T v)) (ψ v))) ∧
      (∀u x y,(F u).Adj x.val y.val→Sum.inl ({ψ u x,ψ u y}:Finset (Fin n))∉Reserve) ∧
      (∀u x y,(F u).Adj x.val y.val→s(ψ u x,ψ u y)∉Del.edgeFinset)) :=by
  obtain ⟨εAbs,ζAbs,δAbs,hεAbs,hζAbs,hδAbs,βconfig,hβconfig,hCommon⟩:=
    long_assigned_vortex_reference_manuscript_matching_and_partials r h k₀ Qpow hr hm hlen αRef ρ₀ sstar tstar kstar tol χActive Qexp pstarRef ζActive
      hQpow hQexp hαRef hαRef1 hρ₀ hsstar hsstar1 htstar htstar1 horder hkstar hmargin htol hχActive hpstarRef hpstarBound hζActive
  refine ⟨εAbs,ζAbs,δAbs,hεAbs,hζAbs,hδAbs,βconfig,hβconfig,?_⟩
  intro εref δref χ β ε hεref hδref hχ hβ hβα hβ1 hβε hε hε1 ε₀ hε₀ hgap d hd
  obtain ⟨m₀,hm₀,hCommon⟩:=hCommon εref δref χ β ε hεref hδref hχ hβ hβα hβ1 hβε hε hε1 ε₀ hε₀ hgap d hd
  refine ⟨m₀,hm₀,?_⟩
  intro size
  obtain ⟨a₀,b₀,e₀,hCommon⟩:=hCommon size
  refine ⟨a₀,b₀,e₀,?_⟩
  intro f₀
  obtain ⟨n₀,hn₀,hCommon⟩:=hCommon f₀
  refine ⟨n₀,hn₀,?_⟩
  intro K hK3 θ BM hθpos hθ hBM BO hBO alpha γ eps lam heps heps1 hγε hlam hlamθ hepsAssign halpha halphaMass hγ m ni hni
  obtain ⟨η,hη,t₀,τ₀,Δ,ξ,ht₀,hτ₀,hτhalf,hΔ,hξ,hξeps,N,hCommon⟩:=
    hCommon K hK3 θ BM hθpos hθ hBM BO hBO alpha γ eps lam heps heps1 hγε hlam hlamθ hepsAssign halpha halphaMass hγ
  refine ⟨η,hη,t₀,τ₀,Δ,ξ,ht₀,hτ₀,hτhalf,hΔ,hξ,hξeps,N,?_⟩
  intro n hn U _ _ F hF Allowed hAllowed P Dnat vsize hreg hDnat hmind hrlo hrhi hcut hclass hmV hvN Q π hpres hnoshort L hL τ A weight hw hDlo hDhi w hw0 hwupper huv εHost hεHost he hbudgetV hbudgetE hτnonneg hτbound hLterminal hεAbs' hAbsSize F₀ hF₀
  intro ρ D hsize t tHub b a p₁ k₁ p₂ k₂ udens q s hLaw μ f pstar BMseed BOseed Wm Wo C ℓ W R Pair Kpair failure Ret ν hpRef hkRef htRef Eref
  have hnpos:0<n:=by omega
  letI : Nonempty (Fin n):=⟨⟨0,hnpos⟩⟩
  have hh:=hCommon n hn U F hF Allowed hAllowed P Dnat vsize hreg hDnat hmind hrlo hrhi hcut hclass hmV hvN Q π hpres hnoshort L hL τ A weight hw hDlo hDhi w hw0 hwupper huv εHost hεHost he hbudgetV hbudgetE hτnonneg hτbound hpRef hkRef htRef
  obtain ⟨z,hz,hEref,hSpoke,hCount,hM,hO,hload,hMass,herror,hMatch⟩:=hh
  have hselect:=marked_vortex_preselect_absorber_from_joint_sample r h d αRef βconfig εref δref tol ζActive ζAbs tstar εAbs
    hζAbs.le size a₀ b₀ e₀ f₀ P Dnat vsize β ε Q π hpres L hLterminal (1/100) p₁ k₁ q s false false ⟨f z.1,z.2⟩
    hreg (by simpa using hnpos) hDnat hrhi hε.le hεAbs' hAbsSize hEref F₀ hF₀
  refine ⟨z,hz,hEref,?_,hSpoke,hCount,hM,hO,hload,hMass,herror,hMatch⟩
  exact hselect
end Oberwolfach
