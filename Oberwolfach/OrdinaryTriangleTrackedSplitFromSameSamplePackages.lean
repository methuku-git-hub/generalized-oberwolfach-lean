module

public import Oberwolfach.OrdinaryTriangleLocalSharpPackage
public import Oberwolfach.OrdinaryTriangleNumericCoreThresholdSelection
public import Oberwolfach.OrdinaryTrackedSelectedCostSplitCertificates

@[expose] public section
/-! One raw outcome, its level and endpoint events, and local sharp packages
for the initial host and every later history give the tracked split wheel
certificates with the same ordinary and deeper cost schedules. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 80000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_tracked_split_from_same_sample_packages
    {n q:ℕ} (β ε ρ₀ α pmin εrows tpot lamInner:ℝ) (d k:ℕ)
    (ω βout b Bweight hpack δpack εstar cLinear bHub BHub ηhub:ℝ)
    (p βeGeo βhGeo ν cap τ eps ellCap:ℝ) (M v₀:ℕ)
    (hcert:OrdinaryTriangleNumericCoreAfterThreshold β ε ρ₀ α pmin εrows tpot lamInner d k
      ω βout b Bweight hpack δpack εstar cLinear bHub BHub ηhub p βeGeo βhGeo ν cap τ eps ellCap M v₀)
    (P S:SimpleGraph (Fin n)) (D mv:ℕ) (Vor:Vortex (Fin q) P D β ε mv)
    (π:Equiv.Perm (Fin n)) (hπ:∀i x,π x∈Vor.extendedVertices i↔x∈Vor.extendedVertices i)
    (Fs:Fin q→SimpleGraph (Fin n)) (C:∀u,Finset (Fs u).ConnectedComponent)
    (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (Kabs:Finset (Sym2 (Fin n)⊕(Fin n×Fin q)))
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (coins:Sym2 (Fin n)→Bool) (s:Fin q→Bool→ℝ)
    (θhost pR pH εR εH βeParent βhParent rate ξroot:ℝ)
    (hreg:P.IsRegularOfDegree D) (hn:0<n) (hD:(n:ℝ)/2≤D)
    (hρlo:ρ₀ ≤ initialIndexDensity (Fin q) D) (hρhi:initialIndexDensity (Fin q) D≤1)
    (hv:v₀≤mv) (hterminal:(M:ℝ)≤ε*mv/2)
    (hθ:cycleThreshold 3≤θhost) (hdegree:(θhost+α)*(n:ℝ)≤D)
    (hpR:pmin≤pR) (hpR1:pR≤1) (hpH:pmin≤pH) (hpH1:pH≤1)
    (hpEq:pR=initialIndexDensity (Fin q) D*pH)
    (hεR:0≤εR) (hRrows:2*εR≤εrows) (hεH:0≤εH) (hHrows:2*εH≤εrows)
    (hbudgetE:βeGeo+3*max cap ellCap≤βeParent) (hbudgetH:βhGeo+2*ellCap≤βhParent)
    (hfinish:ν+cap+4*p≤rate)
    (pstar βP ηP ηH βH cParent Bparent εTri δref href κ aLoad bInner BInner ηInner capInner βeInner βhInner:ℝ)
    (weightTri:∀i,OrdinaryCycle (P.comap (markedVortexVertexEmbedding Vor i)) 3→ℝ)
    (endpointWeight:∀i,markedVortexVertexType Vor i→Sym2 (markedVortexVertexType Vor i⊕markedVortexHubType Vor i)→ℝ):
    let raw:=fun e=>expandedOrdinarySelectedCollapse e (σ e);
    let Bad:=permutationConflictGraph π (3*d);
    let Q:=S\ordinaryEmbeddedComplements Fs C f;let H:=fun v u=>v∉Set.range (f u);
    let Gstart:=Q\ordinaryResourceRim Q Kabs;let Hstart:=fun v u=>H v u∧¬(Sum.inr (v,u)∈Kabs);
    let X:=fun i=>Vor.extendedVertices (i+1);let T:=fun i=>Vor.extendedVertices (i+2);
    let Z:=fun i=>Vor.extendedIndices (i+1);let W:=fun i=>Vor.extendedIndices (i+2);
    let cost:=ordinaryVortexSelectedCost Vor rate;let deepCost:=ordinaryFineDeepCost Vor ξroot;
    let Local:=fun (i:ℕ) (G:SimpleGraph (markedVortexVertexType Vor i))
        (Hs:markedVortexVertexType Vor i→markedVortexHubType Vor i→Prop)=>
      let fv:=markedVortexVertexEmbedding Vor i;let gu:=markedVortexHubEmbedding Vor i;
      let I:=markedVortexInnerVertices Vor i;let Tloc:=ordinaryVortexBufferedVertices Vor i 2;
      let B:=markedVortexInnerHubs Vor i;let Wloc:=ordinaryVortexBufferedHubs Vor i 2;
      OrdinaryTriangleLocalSharpPackage (P.comap fv) G (Bad.comap fv) Hs I Tloc B Wloc
        (markedVortexPermutation Vor π hπ i) d k (by omega) (fun u=>s (gu u)) false (ordinaryRawRestrictPair fv gu raw)
        α ω βout b Bweight hpack δpack εstar cLinear p τ eps bHub BHub ηhub
        pR pH (θhost+α-β/2) (εR*I.card) (εH*B.card) βeParent βhParent
        ξroot aLoad ellCap cap βeGeo βhGeo lamInner ε;
    (∀i,i<Vor.length→OrdinaryTriangleSelectedSampleLevelData n q D mv k d β ε P Vor π hπ
      α ρ₀ pstar βP ηP ηH βH cParent Bparent εTri δref href pR pH pmin κ aLoad εR εH
      bInner BInner ηInner capInner βeInner βhInner (fun _=>θhost+α-β/2)
      (fun t=>εR*(markedVortexInnerVertices Vor t).card) (fun t=>εH*(markedVortexInnerHubs Vor t).card)
      s false raw coins i (weightTri i))→
    (∀i,i<Vor.length→EndpointPhysicalParentWeights (P.comap (markedVortexVertexEmbedding Vor i))
      (markedVortexInnerVertices Vor i) (markedVortexInnerVertices Vor i)ᶜ (endpointWeight i))→
    (∀i,i<Vor.length→EndpointPhysicalPotentialEvent (P.comap (markedVortexVertexEmbedding Vor i))
      (Bad.comap (markedVortexVertexEmbedding Vor i)) (markedVortexInnerVertices Vor i) (markedVortexInnerHubs Vor i)
      (markedVortexInnerVertices Vor i)ᶜ (markedVortexPermutation Vor π hπ i) d false (endpointWeight i) pR pH tpot
      (ordinaryRawRestrictPair (markedVortexVertexEmbedding Vor i) (markedVortexHubEmbedding Vor i) raw))→
    (let fv:=markedVortexVertexEmbedding Vor 0;let gu:=markedVortexHubEmbedding Vor 0;
      Local 0 (Gstart.comap fv) (fun v u=>Hstart (fv v) (gu u)))→
    (∀i,i+1<Vor.length→∀R (G:SimpleGraph (Fin n)) (Hs:Fin n→Fin q→Prop),
      OrdinaryUniformProtectedBalanceHistory Gstart Hstart X T Z W cost deepCost 3 (i+1) Vor.length R
        (fun t=>Vor.extendedVertices (t+2)) (fun t=>Vor.extendedVertices (t+1)) (fun t=>Vor.extendedIndices (t+2))
        (fun t=>Finset.Icc (t+3-2) t) (fun _ _=>0) (fun _ _=>0)→
      ordinaryHostResources G Hs=R→G≤Q→(∀v u,Hs v u→H v u)→
      (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
      (∀u,3∣(Finset.univ.filter (fun v=>Hs v u)).card)→
      let fv:=markedVortexVertexEmbedding Vor (i+1);let gu:=markedVortexHubEmbedding Vor (i+1);
      Local (i+1) (G.comap fv) (fun v u=>Hs (fv v) (gu u)))→
    OrdinaryTrackedSplitWheelCertificatesAt P S Bad Fs C 3 Kabs D mv β ε Vor Vor.length cost deepCost f :=by
  intro raw Bad Q H Gstart Hstart X T Z W cost deepCost Local hlevels hparents hevents hinit hlater
  apply ordinary_tracked_selected_cost_split_certificates P S Bad Fs C 3 Kabs D mv β ε Vor Vor.length rate ξroot f
  · let fv:=markedVortexVertexEmbedding Vor 0
    let gu:=markedVortexHubEmbedding Vor 0
    have hpkg:=hinit
    dsimp [Local,OrdinaryTriangleLocalSharpPackage] at hpkg
    obtain ⟨Ledit,rateParent,hL0,hrate,hcore⟩:=hpkg
    have hh:=hcert n q D mv P hreg hn hD hρlo hρhi hv hterminal Vor π hπ θhost pR pH εR εH Ledit rateParent βeParent βhParent
      hθ hdegree hpR hpR1 hpH hpH1 hpEq hεR hRrows hεH hHrows hL0 hrate 0 Vor.length_pos
      pstar βP ηP ηH βH cParent Bparent εTri δref href κ aLoad bInner BInner ηInner capInner βeInner βhInner
      (fun _=>θhost+α-β/2) (fun t=>εR*(markedVortexInnerVertices Vor t).card)
      (fun t=>εH*(markedVortexInnerHubs Vor t).card) s false raw coins (weightTri 0) (hlevels 0 Vor.length_pos)
      (Gstart.comap fv) (fun v u=>Hstart (fv v) (gu u)) (endpointWeight 0) ξroot rate
      (hparents 0 Vor.length_pos) (hevents 0 Vor.length_pos)
      (by convert hcore using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _) hbudgetE hbudgetH hfinish
    convert hh using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
  · intro i hi R G Hs hhist hstate hG hH hbal hdiv
    let fv:=markedVortexVertexEmbedding Vor (i+1)
    let gu:=markedVortexHubEmbedding Vor (i+1)
    have hpkg:=hlater i hi R G Hs hhist hstate hG hH hbal hdiv
    dsimp [Local,OrdinaryTriangleLocalSharpPackage] at hpkg
    obtain ⟨Ledit,rateParent,hL0,hrate,hcore⟩:=hpkg
    have hh:=hcert n q D mv P hreg hn hD hρlo hρhi hv hterminal Vor π hπ θhost pR pH εR εH Ledit rateParent βeParent βhParent
      hθ hdegree hpR hpR1 hpH hpH1 hpEq hεR hRrows hεH hHrows hL0 hrate (i+1) hi
      pstar βP ηP ηH βH cParent Bparent εTri δref href κ aLoad bInner BInner ηInner capInner βeInner βhInner
      (fun _=>θhost+α-β/2) (fun t=>εR*(markedVortexInnerVertices Vor t).card)
      (fun t=>εH*(markedVortexInnerHubs Vor t).card) s false raw coins (weightTri (i+1)) (hlevels (i+1) hi)
      (G.comap fv) (fun v u=>Hs (fv v) (gu u)) (endpointWeight (i+1)) ξroot rate
      (hparents (i+1) hi) (hevents (i+1) hi)
      (by convert hcore using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _) hbudgetE hbudgetH hfinish
    convert hh using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
end Oberwolfach
