module

public import Oberwolfach.OrdinaryVortexTwoStepSharpGeometryAtThresholdBeforeSampling
public import Oberwolfach.OrdinaryVortexTraceFullParentGeneralFineSharpReference
public import Oberwolfach.OrdinaryInducedBalanceToSpanning
public import Oberwolfach.OrdinaryDeepTracePairingParentAt
public import Oberwolfach.OrdinaryVortexUniformTwoStepBalanceFromInitial
public import Oberwolfach.OrdinaryVortexUniformTwoStepDeepBalance
public import Oberwolfach.OrdinaryDeepTraceFineCoverAtLocalBalance
public import Oberwolfach.OrdinaryDeepTraceCoverAndSeparatedBalanceOrdered

@[expose] public section
/-! Apply the preselected cover and balance callbacks to one protected trace
and the same sampled outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_deep_trace_fine_sharp_reference_pairing_from_geometry_rates_before_sampling
    (mWheel d:ℕ) (hmWheel:3≤mWheel) (ρ₀ pmin hmin href δcut ζcut εcut ζlimit εsample:ℝ)
    (ε ξ aLoad a ρ θ β η ηProfile α ζ cBoundary δ rate C rateParent:ℝ) (mBalance mCover mInitial:ℕ) (ηInitial δInitial:ℝ)
    (hInitialAt:OrdinaryVortexInitialAmbientBalanceAt ε ρ₀ α pmin hmin ηInitial cBoundary δInitial d β mInitial)
    (hbalance:OrdinaryDeepTraceSeparatedBalanceAt ε ρ₀ α pmin hmin ηProfile ζ cBoundary δ rate d 2 β C mBalance)
    (hcover:OrdinaryDeepTraceFineCoverAtLocalBalance mWheel 0 2 ρ₀ hmin href δcut ζcut εcut ζlimit εsample ε ξ aLoad a ρ θ β η d mCover)
    (hζlim:ζ≤ζlimit) (hζrate:ζ≤rateParent)
    (hζcut:0≤ζcut) (hεcut:0≤εcut) (hζlimit:0≤ζlimit):
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder U],
    ∀(P JQ G:SimpleGraph V) (JH Hs:V→U→Prop) (D m:ℕ),
      P.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→mBalance≤m→mCover≤m→
    ∀(Q:Vortex U P D β ε m) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (σ:RawWheelOutcome V U Γ Color) (coins:Sym2 V→Bool) (j:Color) (s:U→Color→ℝ)
      (Kres:Finset (Sym2 V⊕(V×U))) (cost:ℕ→ℝ) (i:ℕ),i+1<Q.length→
    ∀(A:Finset (Sym2 V⊕(V×U))) (pR pH θhost εR εH βe βh αcut pstar:ℝ),
    let f:=markedVortexVertexEmbedding Q (i+1);let g:=markedVortexHubEmbedding Q (i+1)
    let I:=markedVortexInnerVertices Q (i+1);let T:=ordinaryVortexBufferedVertices Q (i+1) 2
    let B:=markedVortexInnerHubs Q (i+1);let W:=ordinaryVortexBufferedHubs Q (i+1) 2
    let ρi:=markedVortexPermutation Q π hπ (i+1)
    let Ploc:=P.comap f;let Floc:=(permutationConflictGraph π (3*d)).comap f
    let Gloc:=G.comap f;let Hloc:=fun v u=>Hs (f v) (g u)
    let raw:=ordinaryRawRestrictPair f g σ
    let F:=permutationConflictGraph π (3*d)
    let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j
    let S:=(R\F)\JQ;let H:=fun v u=>J v u∧¬JH v u
    let S₀:=S\ordinaryResourceRim S Kres;let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈Kres)
    let X:=fun k=>Q.extendedVertices (k+1);let Tdeep:=fun k=>Q.extendedVertices (k+2)
    let Z:=fun k=>Q.extendedIndices (k+1);let Wdeep:=fun k=>Q.extendedIndices (k+2)
    let deepCost:=ordinaryFineDeepCost Q ξ;
    let Jwin:=Finset.Icc (i+2-2) i
    let Ledit:=2*((3*d:ℕ):ℝ)+∑j∈Jwin,cost j;
    ∀(ηf εf γpair κpair aPair lamPair bPair Bweight:ℝ) (mPair:ℕ),
    OrdinaryDeepTracePairingParentAt ε ρ₀ α pmin ηProfile ζ cBoundary δ rate ηf εf γpair κpair aPair lamPair bPair Bweight βe βh d mWheel 2 β C mPair→
    mPair≤m→pmin≤pH→εR≤lamPair→εH≤lamPair→
    OrdinaryAdaptiveHubWeightsLevelEvent mWheel Ploc Floc I B ρi d pR pH (θhost+α-β/2)
      (εR*I.card) (εH*B.card) Ledit βe βh bPair Bweight ηf (fun u=>s (g u)) j raw→
    pmin≤pR→pR≤1→hmin≤pH→pH≤1→1/2≤θhost→(θhost+α)*Fintype.card V≤D→
    pR=initialIndexDensity U D*pH→(∀u,s u j=pH)→
    0≤εR→εR≤δ→εR≤εsample→0≤εH→εH≤δ→εH≤εsample→0≤βe→βe≤cBoundary*ε→0≤βh→βh≤cBoundary*ε→
    (∀v∈Q.extendedVertices 1,∀w∈Q.extendedVertices 1,¬JQ.Adj v w)→
    (∀v u,JH v u→¬(v∈Q.extendedVertices 1 ∧ u∈Q.extendedIndices 1))→
    Disjoint Kres (ordinaryRootResources (Q.extendedVertices 1) (Q.extendedIndices 1))→
    OrdinaryFixedVortexRowIndexEvent 3 d εR εH P F D m β ε Q π hπ pR pH s j σ→
    OrdinaryProtectedTrace S₀ H₀ X Tdeep Z Wdeep cost deepCost (i+1) A→ ordinaryHostResources G Hs=A→
    ∀L:ℕ, i<L→(0< initialIndexDensity U D)→0≤β→
    OrdinaryVortexTwoStepRowIndexEvent 3 d εR εH P F D m β ε Q π hπ pR pH s j σ→
    ∀inner cross:ℕ→ℕ→ℝ,
    OrdinaryUniformProtectedBalanceHistory S₀ H₀ X Tdeep Z Wdeep cost deepCost (mWheel+1) (i+1) L A
      (fun t=>Q.extendedVertices (t+2)) (fun t=>Q.extendedVertices (t+1))
      (fun t=>Q.extendedIndices (t+2)) (fun t=>Finset.Icc (t+3-2) t) inner cross→
    (∀t∈Jwin,0≤cost t ∧ cost t≤4*rate*Fintype.card (markedVortexVertexType Q t⊕markedVortexHubType Q t)+C)→
    mInitial≤m→εR≤δInitial→εH≤δInitial→ηInitial≤η→
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
    (∀u,(mWheel+1)∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    OrdinaryFixedVortexDeepCoverEvent mWheel 0 d a aLoad ρ θ P D m β ε Q π hπ j σ→
    OrdinaryInducedRimCutEvent (Q.extendedVertices (i+2)) (sampledOrientation (rawWheelGraph P σ) coins) αcut pstar→
    0<pH→δcut≤min (αcut/32) (pstar/512)→href≤αcut*pstar/64→
    ∀(k:ℕ) (hk:4≤k) (βH ηH B0 βparent εparent ζparent gap lam hRef δparent cweight:ℝ) (N₀:ℕ),
    0≤B0→0<ρ₀→0<pstar→0≤ζparent→1≤N₀→
    OrdinaryGeneralEditScaleAt (mWheel+1) βH ηH B0 (ρ₀/16) pstar βparent εparent ζparent rateParent N₀→
    OrdinaryUniformFineSharpReferenceAtScale mWheel k (by omega) α βparent cweight
      (B0/((ρ₀/16)*pstar^(2*(mWheel+1)-1))) (2*hRef-ζparent) δparent εparent (ρ₀/16) gap lam→
    N₀≤Fintype.card (markedVortexVertexType Q (i+1))→
    ∀(βP ηP row εTri:ℝ) (weight:OrdinaryCycle Ploc (mWheel+1)→ℝ),
    OrdinaryDeepCoverLevelInputs mWheel (2*(3*d)) d α pstar (ρ₀/16) 1 εTri Ploc Floc ρi B pR pH
      (2*(Fintype.card (markedVortexHubType Q (i+1)):ℝ)/initialIndexDensity U D) β→
    pstar≤pR→pstar≤pH→0≤cweight→
    (∀C,cweight/(Fintype.card (markedVortexVertexType Q (i+1)):ℝ)^((mWheel+1)-2)≤weight C ∧
      weight C≤B0/(Fintype.card (markedVortexVertexType Q (i+1)):ℝ)^((mWheel+1)-2))→
    ordinaryCombinedHostEvent mWheel d k hmWheel Ploc Floc ρi (max (1/2) (cycleThreshold (mWheel+1))) α pstar
      βP ηP row ηH βH cweight B0 pR pH weight (fun u=>s (g u)) j raw→
    OrdinaryTriangleReferenceNormalizedCuts Ploc Floc ρi d j δparent hRef raw
      (fun e=>coins (Sym2.map f e))→
    0≤ξ→0≤aLoad→0≤η→
    letI : DecidableEq (markedVortexVertexType Q (i+1)):=Classical.decEq _
    letI : DecidableEq (markedVortexHubType Q (i+1)):=Classical.decEq _
    let bin:=η*I.card;let cin:=ηInitial*I.card+2*deepCost i;
    let deep:ℝ:=(initialIndexDensity U D*pH)*β*T.card+εR*T.card+2*(εH*W.card)+
      3*(2*((3*d:ℕ):ℝ))+2*deepCost i;
    ∀(βout εstar ηpack ξreserve ζout p εout γgeom edit:ℝ) (mGeom:ℕ),
    mGeom≤m→
    OrdinaryVortexTwoStepSharpGeometryAtThresholdBeforeSampling mWheel d k mGeom β ε ρ₀ lam ξreserve ξ aLoad η ηInitial γgeom edit p (βe/2) (βh/2) pH εR εH
      (βparent/2) (cweight*(1-δparent)^mWheel) (B0/((ρ₀/16)*pstar^(2*(mWheel+1)-1)))
      (εparent+gap) (εstar-(εparent+gap)) βout ζout ηpack εout→
    let ell:=max (18*aLoad*Fintype.card (markedVortexVertexType Q (i+1))+3*((W.card:ℝ)+(((0:ℕ):ℝ)+1)*T.card))
      (3*aLoad*Fintype.card (markedVortexVertexType Q (i+1))*((mWheel:ℝ)+1)+(T.card:ℝ)*((mWheel:ℝ)+1));
    let cover:=10*ξ*I.card;let loss:=12*aLoad*Fintype.card (markedVortexVertexType Q (i+1));
    let fout:=deep+2*cover;let binner:=bin+deep+4*cover;let crossout:=cin+deep+loss;
    let Aroot:=Finset.univ\T;let Croot:=Finset.univ\W;
    let Xf:Finset Aroot:=Finset.univ.filter (fun v=>v.val∈I);
    let Zf:Finset Croot:=Finset.univ.filter (fun u=>u.val∈B);
    (∃Droot:OrdinaryRootCoverNonrootData Gloc Floc Hloc I T B W (mWheel+1) cover ell,
      Nonempty (OrdinaryRootCoverSharpReferenceData Ploc Gloc Floc Hloc I T B W (mWheel+1) k (by omega)
        cover ell bin cin deep loss Droot α (ρ₀/16) (βparent/2) βout (cweight*(1-δparent)^mWheel)
        (B0/((ρ₀/16)*pstar^(2*(mWheel+1)-1))) (2*hRef-ζparent) (δparent/2) (εparent+gap)
        εstar ηpack ξreserve ζout p εout fout binner crossout)) ∧
    (T.card:ℝ)≤((βe/2)/4)*Fintype.card (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1)) ∧
    (W.card:ℝ)≤((βh/2)/2)*Fintype.card (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1)) ∧
    0≤(∑t∈Jwin,cost t) ∧
    OrdinaryCleanupParentProfiles Ploc Gloc Floc Hloc ρi d I B pR pH (θhost+α-β/2)
      (εR*I.card) (εH*B.card) Ledit βe βh (fun u=>s (g u)) j raw ∧
    (∀v:I,|((Gloc.induce (I:Set _)).degree v:ℝ)-
      2*(Finset.univ.filter (fun u:B=>Hloc v.val u.val)).card|≤η*I.card) ∧
    Ledit≤rateParent*Fintype.card (markedVortexVertexType Q (i+1)) ∧
    OrdinaryFineWheelCoverResult mWheel 0 ξ aLoad Gloc Floc Hloc I T B W ∧
    (∀v,v∉I→|((Gloc.neighborFinset v∩I).card:ℝ)-2*(B.filter (Hloc v)).card|≤
      ηInitial*I.card+2*deepCost i) ∧
    (∀v,v∉T→|((Gloc.neighborFinset v∩T).card:ℝ)-2*(W.filter (Hloc v)).card|≤
      (initialIndexDensity U D*pH)*β*T.card+εR*T.card+2*(εH*W.card)+
        3*(2*((3*d:ℕ):ℝ))+2*deepCost i) ∧
    Nonempty (MixedFreshPairingParentInsideRoots mWheel (2*(3*d)) γpair κpair bPair Bweight pmin aPair εf ηf
      (spanningRestriction Gloc I) Floc
      (ordinaryPhysicalGraph (spanningRestriction Gloc I) (fun v u=>Hloc v u∧v∈I∧u∈B))
      (ordinaryPhysicalGraph Floc (fun _ _=>False)) (Function.Embedding.inl:markedVortexVertexType Q (i+1)↪_)
      (ordinaryBoundaryHubSet Hloc B I) (fun t=>(ordinaryBoundaryRimSet Gloc I t).image Sum.inl)
      (fun t=>(ordinaryBoundaryRowSet Hloc I B t).image Sum.inr) (fun _=>pH)):=by
  intro V U Γ Color _ _ _ _ _ _ P JQ G JH Hs D m hreg hn hD hρlo hρhi hmB hmC Q π hπ σ coins j s Kres cost i hi
    A pR pH θhost εR εH βe βh αcut pstar f g I T B W ρi Ploc Floc Gloc Hloc raw F R J S H S₀ H₀ X Tdeep Z Wdeep deepCost Jwin Ledit
    ηf εf γpair κpair aPair lamPair bPair Bweight mPair hpairAt hmPair hpHpair hεRlam hεHlam hevent
    hpRlo hpRhi hpHlo hpHhi hθhost hdegree hpEq hs hεR0 hεR hεRsample hεH0 hεH hεHsample hβe0 hβe hβh0 hβh hJQ hJH havoid hgood htrace hstate L hiL hρpos hβ0 hgood2 inner cross huniform hcost hmI hεRinitial hεHinitial hηInitial hbal hdiv hdeep hrim hpH hcut hhref
    k hk βH ηH B0 βparent εparent ζparent gap lam hRef δparent cweight N₀ hB0 hρ₀ hpstar hζparent hN₀ hscale hroot hN
    βP ηP row εTri weight hinputs hpRstar hpHstar hcweight hweight heventParent hcutsParent hξ0 haLoad0 hη0
    bin cin deep βout εstar ηpack ξreserve ζout p εout γgeom edit mGeom hmGeom hGeom
    ell cover loss fout binner crossout Aroot Croot Xf Zf
  obtain ⟨hwin0,hwinI,hwinB,hprofile,hnearProfile,hmarginProfile,hLinner,hLparent⟩:=
    hbalance V U Γ Color P JQ JH D m hreg hn hD hρlo hρhi hmB Q π hπ s j σ
      pR pH θhost εR εH βe βh hpRlo hpRhi hpHlo hθhost hdegree hpEq hs hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh
      Kres hJQ hJH havoid hgood cost deepCost i hi A G Hs htrace hstate hcost
  have hboth:=ordinary_vortex_uniform_two_step_balance_from_initial ε ρ₀ α pmin hmin ηInitial cBoundary δInitial d β mInitial hInitialAt
    P JQ G JH Hs D m hreg hn hD hρlo hρhi hmI Q π hπ pR pH θhost εR εH βe βh s j σ Kres
    hpRlo hpRhi hpHlo hθhost hdegree hεR0 hεRinitial hεH0 hεHinitial hβe0 hβe hβh0 hβh hpEq hs hJQ hJH havoid hgood
    (mWheel+1) i L hi hiL cost deepCost A inner cross huniform hstate
  have hnear:∀v:I,|((Gloc.induce (I:Set _)).degree v:ℝ)-
      2*(Finset.univ.filter (fun u:B=>Hloc v.val u.val)).card|≤η*I.card:=by
    intro v
    have hle:=mul_le_mul_of_nonneg_right hηInitial (show (0:ℝ)≤I.card by positivity)
    have hh:=hboth.1 v
    convert hh.trans hle using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hI0:0≤(I.card:ℝ):=by positivity
  have hW0:0≤(Fintype.card (markedVortexVertexType Q (i+1)):ℝ):=by positivity
  have hLcover:Ledit≤ζlimit*I.card:=hLinner.trans (mul_le_mul_of_nonneg_right hζlim hI0)
  have hLrate:Ledit≤rateParent*Fintype.card (markedVortexVertexType Q (i+1)):=
    hLparent.trans (mul_le_mul_of_nonneg_right hζrate hW0)
  have hL0:0≤Ledit:=by dsimp [Ledit];positivity
  have hh:=hcover V U Γ Color P JQ G JH Hs D m hreg hn hD hρlo hρhi hmC Q π hπ σ coins j s Kres cost deepCost i hi
    A pR pH (θhost+α-β/2) εR εH Ledit βe βh αcut pstar θhost α hpHlo hεRsample hεHsample hLcover
    hprofile rfl hεR0 hεH0 hdegree hpEq hgood hnear htrace hstate hbal hdiv hdeep hrim hpH hpHhi hεcut hζcut hζlimit hL0 hcut hhref
  have hdeepBal:=ordinary_vortex_uniform_two_step_deep_balance P JQ JH D m β ε pR pH εR εH Q π hπ d s j σ Kres
    hn hreg hρpos hβ0 hpH.le hεR0 hεH0 hpEq hJQ hJH havoid hgood2 (mWheel+1) i L hi hiL cost deepCost A G Hs inner cross huniform hstate
  have hpair:=hpairAt V U Γ Color P JQ JH D m hreg hn hD hρlo hρhi hmPair Q π hπ s j σ
    pR pH θhost εR εH hpRlo hpRhi hpHpair hpHhi hθhost hdegree hpEq hs hεR0 hεR hεRlam hεH0 hεH hεHlam
    Kres hJQ hJH havoid hgood cost deepCost i hi A G Hs htrace hstate hcost
    (by convert hevent using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  have hcost_i:0≤cost i:=by
    have hiwin:i∈Jwin:=by simp [Jwin]
    exact (hcost i hiwin).1
  have hLrate':2*((3*d:ℕ):ℝ)+cost i≤rateParent*Fintype.card (markedVortexVertexType Q (i+1)):=by
    simpa [Ledit,Jwin] using hLrate
  have hTX:T⊆I:=(ordinary_vortex_buffered_nested Q (i+1) 2 (by omega)).2.2.1
  have hWZ:W⊆B:=(ordinary_vortex_buffered_nested Q (i+1) 2 (by omega)).2.2.2
  have hdecV:(Classical.decEq (markedVortexVertexType Q (i+1))) = (fun a b=>Subtype.instDecidableEq a b) := Subsingleton.elim _ _
  have hdecU:(Classical.decEq (markedVortexHubType Q (i+1))) = (fun a b=>Subtype.instDecidableEq a b) := Subsingleton.elim _ _
  have hGeo:=hGeom V U P D m hreg hn hD hρlo hρhi hmGeom Q i hi
  simp only [←hdecV,←hdecU] at hGeo
  obtain ⟨hsize,hTcard,hWcard,hdeep0,hbin,hcin,hstatic0,hscaleV,hscaleU⟩:=hGeo
  let Astd:Finset (markedVortexVertexType Q (i+1)):=@SDiff.sdiff _ (@Finset.instSDiff _ (fun a b=>Subtype.instDecidableEq a b)) Finset.univ T
  let Cstd:Finset (markedVortexHubType Q (i+1)):=@SDiff.sdiff _ (@Finset.instSDiff _ (fun a b=>Subtype.instDecidableEq a b)) Finset.univ W
  have hAeq:Aroot=Astd:=by ext x;simp [Aroot,Astd]
  have hCeq:Croot=Cstd:=by ext x;simp [Croot,Cstd]
  have hstatic:OrdinaryNonrootGeometryStatic (mWheel+1) k (ρ₀/16) (βparent/2) βout (cweight*(1-δparent)^mWheel)
      (B0/((ρ₀/16)*pstar^(2*(mWheel+1)-1))) (εparent+gap) εstar ηpack ξreserve ζout p εout fout binner crossout Xf Zf:=by
    have heq:(εparent+gap)+(εstar-(εparent+gap))=εstar:=by ring
    rw [heq] at hstatic0
    dsimp only [Xf,Zf]
    rw [hAeq,hCeq]
    simpa only [Astd,Cstd,T,W,I,B,fout,binner,crossout,cover,loss,bin,cin,deep,deepCost] using hstatic0

  have hinner:=ordinary_induced_balance_to_spanning Gloc Hloc I B bin hbin hnear
  have hRefResult:=ordinary_vortex_trace_full_parent_general_fine_sharp_reference_at_scale mWheel hmWheel
    βH ηH B0 ρ₀ pstar βparent εparent ζparent rateParent N₀ hB0 hρ₀ hpstar hζparent hN₀ hscale
    k hk α cweight hRef δparent gap lam hroot V U Γ Color P JQ JH D m β ε Q π hπ d s j σ coins Kres
    hJQ hJH havoid cost deepCost i A G Hs βP ηP row εTri pR pH weight htrace hstate hN hcost_i hLrate' (by convert hinputs using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    hpRstar hpRhi hpHstar hpHhi hcweight hweight
    (by convert heventParent using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by convert hcutsParent using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) I T B W ξ aLoad bin cin deep
    (ρ₀/16) βout εstar ηpack ξreserve ζout p εout hsize hTX hWZ hξ0 haLoad0 hbin hdeep0 hh hbal hdiv
    (by intro v hv;convert hdeepBal v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro v;convert hinner v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro v hv;convert hboth.2 v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    hstatic
    (by simpa only [ell,T,W,zero_add,one_mul,Nat.cast_ofNat,Nat.cast_zero,Astd,Cstd,←hAeq,←hCeq] using hscaleV)
    (by simpa only [ell,T,W,zero_add,one_mul,Nat.cast_ofNat,Nat.cast_zero,Astd,Cstd,←hAeq,←hCeq] using hscaleU)
  refine ⟨?_,?_,?_,hwin0,?_,?_,hLrate,?_,?_,?_,?_⟩
  · convert hRefResult using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · convert hTcard using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · convert hWcard using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · convert hprofile using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro v;convert hnear v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro v hv
    convert hboth.2 v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro v hv
    convert hdeepBal v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · convert hpair using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
