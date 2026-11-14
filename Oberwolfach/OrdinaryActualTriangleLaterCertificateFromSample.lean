module

public import Oberwolfach.OrdinaryActualTriangleLaterCoreFromSample
public import Oberwolfach.OrdinaryTriangleNumericCoreThresholdSelection
public import Oberwolfach.OrdinaryTriangleSelectedSampleLevelDataFinOfGeneral

@[expose] public section
/-! The selected numerical callback and later sharp data give a wheel
certificate on the same sampled outcome and protected history. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 90000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_actual_triangle_later_certificate_from_sample
    (d:ℕ) (ρ₀ pmin hmin href δcut ζcut εcut ζlimit εsample:ℝ)
    (ε ξ aLoad κ β η ηProfile α ζ cBoundary δ rate C rateParent:ℝ) (mBalance mCover mInitial:ℕ) (ηInitial δInitial:ℝ)
    (hInitialAt:OrdinaryVortexActualInitialAmbientBalanceAt ε ρ₀ α pmin hmin ηInitial cBoundary δInitial d β mInitial)
    (hbalance:OrdinaryActualTraceSeparatedBalanceAt ε ρ₀ α pmin hmin ηProfile ζ cBoundary δ rate d 2 β C mBalance)
    (hcover:OrdinaryActualTraceTriangleFineCoverAtLocalBalance 2 ρ₀ hmin href δcut ζcut εcut ζlimit εsample ε ξ aLoad κ β η d mCover)
    (hζlim:ζ≤ζlimit) (hζrate:ζ≤rateParent)
    (hζcut:0≤ζcut) (hεcut:0≤εcut) (hζlimit:0≤ζlimit):
    ∀(n q:ℕ),
    letI : DecidableEq (Fin n):=Classical.decEq _
    letI : DecidableEq (Fin q):=Classical.decEq _
    ∀(P Gbase G:SimpleGraph (Fin n)) (Hbase Hs:(Fin n)→(Fin q)→Prop) (D m:ℕ),
      Gbase≤P→P.IsRegularOfDegree D→0<Fintype.card (Fin n)→(Fintype.card (Fin n):ℝ)/2≤D→
      ρ₀≤ initialIndexDensity (Fin q) D→initialIndexDensity (Fin q) D≤1→mBalance≤m→mCover≤m→
    ∀(Q:Vortex (Fin q) P D β ε m) (π:Equiv.Perm (Fin n))
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (σ:RawWheelOutcome (Fin n) (Fin q) Bool Bool) (coins:Sym2 (Fin n)→Bool) (j:Bool) (s:(Fin q)→Bool→ℝ)
      (Kres:Finset (Sym2 (Fin n)⊕((Fin n)×(Fin q)))) (cost deepCost:ℕ→ℝ) (i:ℕ),i+1<Q.length→
    ∀(A:Finset (Sym2 (Fin n)⊕((Fin n)×(Fin q)))) (pR pH θhost εR εH βe βh αcut pstar:ℝ),
    let f:=markedVortexVertexEmbedding Q (i+1);let g:=markedVortexHubEmbedding Q (i+1)
    let I:=markedVortexInnerVertices Q (i+1);let T:=ordinaryVortexBufferedVertices Q (i+1) 2
    let B:=markedVortexInnerHubs Q (i+1);let W:=ordinaryVortexBufferedHubs Q (i+1) 2
    let ρi:=markedVortexPermutation Q π hπ (i+1)
    let Ploc:=P.comap f;let Floc:=(permutationConflictGraph π (3*d)).comap f
    let Gloc:=G.comap f;let Hloc:=fun v u=>Hs (f v) (g u)
    let raw:=ordinaryRawRestrictPair f g σ
    let F:=permutationConflictGraph π (3*d)
    let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j
    let S:=Gbase;let H:=Hbase
    let S₀:=S\ordinaryResourceRim S Kres;let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈Kres)
    let X:=fun k=>Q.extendedVertices (k+1);let Tdeep:=fun k=>Q.extendedVertices (k+2)
    let Z:=fun k=>Q.extendedIndices (k+1);let Wdeep:=fun k=>Q.extendedIndices (k+2)
    let Jwin:=Finset.Icc (i+2-2) i
    let Ledit:=2*((3*d:ℕ):ℝ)+∑j∈Jwin,cost j;
    ∀(ηf bPair Bweight capHub:ℝ),ζ≤capHub→
    pmin≤pR→pR≤1→hmin≤pH→pH≤1→1/2≤θhost→(θhost+α)*Fintype.card (Fin n)≤D→
    pR=initialIndexDensity (Fin q) D*pH→(∀u,s u j=pH)→
    0≤εR→εR≤δ→εR≤εsample→0≤εH→εH≤δ→εH≤εsample→0≤βe→βe≤cBoundary*ε→0≤βh→βh≤cBoundary*ε→
    (∀v∈Q.extendedVertices 1,∀w∈Q.extendedVertices 1,(R\F).Adj v w↔Gbase.Adj v w)→
    (∀v∈Q.extendedVertices 1,∀u∈Q.extendedIndices 1,J v u↔Hbase v u)→
    Disjoint Kres (ordinaryRootResources (Q.extendedVertices 1) (Q.extendedIndices 1))→
    OrdinaryProtectedTrace S₀ H₀ X Tdeep Z Wdeep cost deepCost (i+1) A→ ordinaryHostResources G Hs=A→
    ∀L:ℕ, i<L→(0< initialIndexDensity (Fin q) D)→0≤β→β≤1/4→0<ε→0<m→
    ∀inner cross:ℕ→ℕ→ℝ,
    OrdinaryUniformProtectedBalanceHistory S₀ H₀ X Tdeep Z Wdeep cost deepCost (2+1) (i+1) L A
      (fun t=>Q.extendedVertices (t+2)) (fun t=>Q.extendedVertices (t+1))
      (fun t=>Q.extendedIndices (t+2)) (fun t=>Finset.Icc (t+3-2) t) inner cross→
    (∀t∈Jwin,0≤cost t ∧ cost t≤4*rate*Fintype.card (markedVortexVertexType Q t⊕markedVortexHubType Q t)+C)→
    mInitial≤m→εR≤δInitial→εH≤δInitial→ηInitial≤η→
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
    (∀u,(2+1)∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    0<pH→δcut≤min (αcut/32) (pstar/512)→href≤αcut*pstar/64→
    ∀(k:ℕ) (hk:4≤k) (βH ηH B0 βparent εparent ζparent gap lam hRef δparent cweight:ℝ) (N₀:ℕ),
    0≤B0→0<ρ₀→0<pstar→0≤ζparent→1≤N₀→
    OrdinaryTriangleEditScaleAt βH ηH B0 (ρ₀/16) pstar βparent εparent ζparent rateParent N₀→
    OrdinaryUniformFineSharpReferenceAtScaleGeneralLoad 2 k 0 (by decide) α βparent cweight
      (B0/((ρ₀/16)*pstar^(2*(2+1)-1))) (2*hRef-ζparent) δparent εparent (ρ₀/16) gap lam→
    N₀≤Fintype.card (markedVortexVertexType Q (i+1))→
    ∀(βP ηP εTri:ℝ) (weight:OrdinaryCycle Ploc (2+1)→ℝ),
    αcut=min (α/4) (1/4:ℝ)→pmin=pstar→
    OrdinaryTriangleSelectedSampleLevelDataGeneral D m k d β ε P Q π hπ
      α ρ₀ pstar βP ηP ηH βH cweight B0 εTri δparent hRef
      pR pH pmin κ aLoad εR εH bPair Bweight ηf capHub βe βh
      (fun _=>θhost+α-β/2) (fun t=>εR*(markedVortexInnerVertices Q t).card)
      (fun t=>εH*(markedVortexInnerHubs Q t).card) s j σ coins (i+1) weight→
    pstar≤pR→pstar≤pH→0≤cweight→
    (T.card:ℝ)+W.card≤lam*Fintype.card (markedVortexVertexType Q (i+1))→
    0≤ξ→0≤aLoad→0≤η→
    letI : DecidableEq (markedVortexVertexType Q (i+1)):=Classical.decEq _
    letI : DecidableEq (markedVortexHubType Q (i+1)):=Classical.decEq _
    let bin:=η*I.card;let cin:=ηInitial*I.card+2*deepCost i;
    let deep:ℝ:=(initialIndexDensity (Fin q) D*pH)*β*T.card+εR*T.card+2*(εH*W.card)+
      3*(2*((3*d:ℕ):ℝ))+2*deepCost i;
    0≤deep→
    ∀(ωout βout εstar ηpack ξreserve ζout p εout lamGeo ellCap cap βeGeo βhGeo hpack cLinear τ:ℝ),
    let ell:=max (18*aLoad*Fintype.card (markedVortexVertexType Q (i+1))+3*((W.card:ℝ)+(((0:ℕ):ℝ)+1)*T.card))
      (3*aLoad*Fintype.card (markedVortexVertexType Q (i+1))*((2:ℝ)+1)+(T.card:ℝ)*((2:ℝ)+1));
    let cover:=10*ξ*I.card;let loss:=12*aLoad*Fintype.card (markedVortexVertexType Q (i+1));
    let fout:=deep+2*cover;let binner:=bin+deep+4*cover;let crossout:=cin+deep+loss;
    let Aroot:=Finset.univ\T;let Croot:=Finset.univ\W;
    let Xf:Finset Aroot:=Finset.univ.filter (fun v=>v.val∈I);
    let Zf:Finset Croot:=Finset.univ.filter (fun u=>u.val∈B);
    OrdinaryNonrootGeometryStatic (2+1) k ωout (βparent/2) βout (cweight*(1-δparent)^2)
      (B0/((ρ₀/16)*pstar^(2*(2+1)-1))) (εparent+gap) εstar ηpack ξreserve ζout p εout fout binner crossout Xf Zf→
    ell+(p+εout)*Fintype.card (Aroot⊕Croot)≤ζout*Fintype.card Aroot→
    ell+(p+εout)*Fintype.card (Aroot⊕Croot)≤ζout*Fintype.card Croot→
    0≤rateParent→G≤P\F→0≤lamGeo→lamGeo≤1/4→
    (T.card:ℝ)+W.card≤lamGeo*Fintype.card (markedVortexVertexType Q (i+1))→
    0≤ellCap→0≤cap→max (18*aLoad+3*lamGeo) ((3*aLoad+lamGeo)*3)≤ellCap→10*ξ≤cap→
    hpack≤(2*hRef-ζparent)-ξreserve-ζout→0≤βeGeo→
    (T.card:ℝ)≤(βeGeo/4)*Fintype.card (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1))→
    (W.card:ℝ)≤(βhGeo/2)*Fintype.card (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1))→
    ηpack=cLinear*τ→
    ∀(εrows tpot lamInner ν rateFinish:ℝ) (M v₀:ℕ),
    OrdinaryTriangleNumericCoreAfterThreshold β ε ρ₀ α pmin εrows tpot lamInner d k ωout βout
      (cweight*(1-δparent)^2) (B0/((ρ₀/16)*pstar^(2*3-1))) hpack (δparent/2) εstar cLinear
      bPair Bweight ηf p βeGeo βhGeo ν cap τ εout ellCap M v₀→
    cycleThreshold 3≤θhost→pmin≤pH→2*εR≤εrows→2*εH≤εrows→ rateParent≤lamInner*ε/4→
    v₀≤m→(M:ℝ)≤ε*m/2→
    ∀endpointWeight:markedVortexVertexType Q (i+1)→Sym2 (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1))→ℝ,
    EndpointPhysicalParentWeights Ploc I Iᶜ endpointWeight→
    EndpointPhysicalPotentialEvent Ploc Floc I B Iᶜ ρi d j endpointWeight pR pH tpot raw→
    βeGeo+3*max cap ellCap≤βe→βhGeo+2*ellCap≤βh→ν+cap+4*p≤rateFinish→
    OrdinaryWheelLikelySeparateCostsCertificate Gloc Floc Hloc I T B W 3
      (rateFinish*Fintype.card (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1))) (10*ξ*I.card) :=by
  intro n q P Gbase G Hbase Hs D m hGbase hreg hn hD hρlo hρhi hmB hmC Q π hπ σ coins j s Kres cost deepCost i hi
    A pR pH θhost εR εH βe βh αcut pstar f g I T B W ρi Ploc Floc Gloc Hloc raw F R J S H S₀ H₀ X Tdeep Z Wdeep Jwin Ledit
    ηf bPair Bweight capHub hζcap
    hpRlo hpRhi hpHlo hpHhi hθhost hdegree hpEq hs hεR0 hεR hεRsample hεH0 hεH hεHsample hβe0 hβe hβh0 hβh hPairRim hPairSpoke havoid htrace hstate L hiL hρpos hβ0 hβ1 hεpos hm0 inner cross huniform hcost hmI hεRinitial hεHinitial hηInitial hbal hdiv hpH hcut hhref
    k hk βH ηH B0 βparent εparent ζparent gap lam hRef δparent cweight N₀ hB0 hρ₀ hpstar hζparent hN₀ hscale hroot hN
    βP ηP εTri weight hαcut hpminEq hsample hpRstar hpHstar hcweight hsize hξ0 haLoad0 hη0
    bin cin deep hdeep0 ωout βout εstar ηpack ξreserve ζout p εout lamGeo ellCap cap βeGeo βhGeo hpack cLinear τ ell cover loss fout binner crossout Aroot Croot Xf Zf
    hstatic hscaleV hscaleU hRate0 hhostGlobal hlamGeo hlam4 hrootGeo hellCap hcap hell hξcap hpackcut hβeGeo hT hW hηpack
    εrows tpot lamInner ν rateFinish M v₀ hcert hθcycle hpminH hRrows hHrows hRateInner hv₀ hterminal endpointWeight parent event hbudgetE hbudgetH hfinish
  have hcore:=ordinary_actual_triangle_later_core_from_sample_level d ρ₀ pmin hmin href δcut ζcut εcut ζlimit εsample
    ε ξ aLoad κ β η ηProfile α ζ cBoundary δ rate C rateParent mBalance mCover mInitial ηInitial δInitial
    hInitialAt hbalance hcover hζlim hζrate hζcut hεcut hζlimit
    (Fin n) (Fin q) Bool Bool P Gbase G Hbase Hs D m hGbase hreg hn hD hρlo hρhi hmB hmC
    Q π hπ σ coins j s Kres cost deepCost i hi A pR pH θhost εR εH βe βh αcut pstar ηf bPair Bweight capHub hζcap
    hpRlo hpRhi hpHlo hpHhi hθhost hdegree hpEq hs hεR0 hεR hεRsample hεH0 hεH hεHsample hβe0 hβe hβh0 hβh
    hPairRim
    (by convert hPairSpoke using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    (by convert havoid using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    (by convert htrace using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    (by convert hstate using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    L hiL hρpos hβ0 hβ1 hεpos hm0 inner cross
    (by convert huniform using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    (by convert hcost using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    hmI hεRinitial hεHinitial hηInitial
    (by intro v;convert hbal v using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    (by intro u;convert hdiv u using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    hpH hcut hhref
    k hk βH ηH B0 βparent εparent ζparent gap lam hRef δparent cweight N₀ hB0 hρ₀ hpstar hζparent hN₀ hscale hroot hN
    βP ηP εTri weight hαcut hpminEq
    (by convert hsample using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    hpRstar hpHstar hcweight
    (by convert hsize using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    hξ0 haLoad0 hη0
    (by convert hdeep0 using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    ωout βout εstar ηpack ξreserve ζout p εout lamGeo ellCap cap βeGeo βhGeo hpack cLinear τ
    hstatic
    (by convert hscaleV using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    (by convert hscaleU using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    hRate0 hhostGlobal hlamGeo hlam4
    (by convert hrootGeo using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    hellCap hcap hell hξcap hpackcut hβeGeo
    (by convert hT using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    (by convert hW using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    hηpack
  have hfin:=ordinary_triangle_selected_sample_level_fin_of_general n q D m k d β ε P Q π hπ
    α ρ₀ pstar βP ηP ηH βH cweight B0 εTri δparent hRef pR pH pmin κ aLoad εR εH
    bPair Bweight ηf capHub βe βh (fun _=>θhost+α-β/2)
    (fun t=>εR*(markedVortexInnerVertices Q t).card) (fun t=>εH*(markedVortexInnerHubs Q t).card)
    s j σ coins (i+1) weight
    (by convert hsample using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
  have hL0:0≤Ledit:=by
    have hs0:0≤∑t∈Jwin,cost t:=Finset.sum_nonneg (fun t ht=>(hcost t ht).1)
    dsimp [Ledit];positivity
  have hh:=hcert n q D m P hreg (by simpa using hn) (by simpa using hD) hρlo hρhi hv₀ hterminal Q π hπ
    θhost pR pH εR εH Ledit rateParent βe βh hθcycle (by simpa using hdegree)
    hpRlo hpRhi hpminH hpHhi hpEq hεR0 hRrows hεH0 hHrows hL0 hRateInner (i+1) hi
    pstar βP ηP ηH βH cweight B0 εTri δparent hRef κ aLoad bPair Bweight ηf capHub βe βh
    (fun _=>θhost+α-β/2) (fun t=>εR*(markedVortexInnerVertices Q t).card)
    (fun t=>εH*(markedVortexInnerHubs Q t).card) s j σ coins weight hfin Gloc Hloc endpointWeight ξ rateFinish
    (by convert parent using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    (by convert event using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    (by convert hcore using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    hbudgetE hbudgetH hfinish
  convert hh using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
end Oberwolfach
