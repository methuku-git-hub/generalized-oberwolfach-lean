module

public import Oberwolfach.OrdinaryTriangleSelectedSampleLevelDataGeneral
public import Oberwolfach.OrdinaryVortexLocalTriangleFineSharpSeparateCross
public import Oberwolfach.OrdinaryActualTraceTriangleFineCoverShared
public import Oberwolfach.OrdinaryActualTraceBalanceAndFineCoverAt
public import Oberwolfach.OrdinaryActualInitialAmbientBalance
public import Oberwolfach.OrdinaryVortexActualUniformTwoStepBalance
public import Oberwolfach.OrdinaryVortexActualUniformTwoStepDeepBalance
public import Oberwolfach.OrdinaryProtectedPairTraceHubBalance
public import Oberwolfach.OrdinaryProtectedPairTracePhysicalEdit
public import Oberwolfach.OrdinaryVortexLocalSharpSeparateCross
public import Oberwolfach.OrdinaryUniformInnerHubEvent
public import Oberwolfach.OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent
public import Oberwolfach.OrdinaryProtectedTraceHostLe
public import Oberwolfach.OrdinaryVortexTraceFullParentGeneralFineSharpReferenceGeneralLoad
public import Oberwolfach.OrdinaryInducedBalanceToSpanning
public import Oberwolfach.OrdinaryDeepTracePairingParentAt
public import Oberwolfach.OrdinaryVortexUniformTwoStepBalanceFromInitial
public import Oberwolfach.OrdinaryVortexUniformTwoStepDeepBalance
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

theorem ordinary_actual_triangle_trace_sharp_from_sample_level
    (d:ℕ) (ρ₀ pmin hmin href δcut ζcut εcut ζlimit εsample:ℝ)
    (ε ξ aLoad κ β η ηProfile α ζ cBoundary δ rate C rateParent:ℝ) (mBalance mCover mInitial:ℕ) (ηInitial δInitial:ℝ)
    (hInitialAt:OrdinaryVortexActualInitialAmbientBalanceAt ε ρ₀ α pmin hmin ηInitial cBoundary δInitial d β mInitial)
    (hbalance:OrdinaryActualTraceSeparatedBalanceAt ε ρ₀ α pmin hmin ηProfile ζ cBoundary δ rate d 2 β C mBalance)
    (hcover:OrdinaryActualTraceTriangleFineCoverAtLocalBalance 2 ρ₀ hmin href δcut ζcut εcut ζlimit εsample ε ξ aLoad κ β η d mCover)
    (hζlim:ζ≤ζlimit) (hζrate:ζ≤rateParent)
    (hζcut:0≤ζcut) (hεcut:0≤εcut) (hζlimit:0≤ζlimit):
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder U],
    ∀(P Gbase G:SimpleGraph V) (Hbase Hs:V→U→Prop) (D m:ℕ),
      Gbase≤P→P.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→mBalance≤m→mCover≤m→
    ∀(Q:Vortex U P D β ε m) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (σ:RawWheelOutcome V U Γ Color) (coins:Sym2 V→Bool) (j:Color) (s:U→Color→ℝ)
      (Kres:Finset (Sym2 V⊕(V×U))) (cost deepCost:ℕ→ℝ) (i:ℕ),i+1<Q.length→
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
    let S:=Gbase;let H:=Hbase
    let S₀:=S\ordinaryResourceRim S Kres;let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈Kres)
    let X:=fun k=>Q.extendedVertices (k+1);let Tdeep:=fun k=>Q.extendedVertices (k+2)
    let Z:=fun k=>Q.extendedIndices (k+1);let Wdeep:=fun k=>Q.extendedIndices (k+2)
    let Jwin:=Finset.Icc (i+2-2) i
    let Ledit:=2*((3*d:ℕ):ℝ)+∑j∈Jwin,cost j;
    ∀(ηf bPair Bweight capHub:ℝ),ζ≤capHub→
    pmin≤pR→pR≤1→hmin≤pH→pH≤1→1/2≤θhost→(θhost+α)*Fintype.card V≤D→
    pR=initialIndexDensity U D*pH→(∀u,s u j=pH)→
    0≤εR→εR≤δ→εR≤εsample→0≤εH→εH≤δ→εH≤εsample→0≤βe→βe≤cBoundary*ε→0≤βh→βh≤cBoundary*ε→
    (∀v∈Q.extendedVertices 1,∀w∈Q.extendedVertices 1,(R\F).Adj v w↔Gbase.Adj v w)→
    (∀v∈Q.extendedVertices 1,∀u∈Q.extendedIndices 1,J v u↔Hbase v u)→
    Disjoint Kres (ordinaryRootResources (Q.extendedVertices 1) (Q.extendedIndices 1))→
    OrdinaryProtectedTrace S₀ H₀ X Tdeep Z Wdeep cost deepCost (i+1) A→ ordinaryHostResources G Hs=A→
    ∀L:ℕ, i<L→(0< initialIndexDensity U D)→0≤β→β≤1/4→0<ε→0<m→
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
    let deep:ℝ:=(initialIndexDensity U D*pH)*β*T.card+εR*T.card+2*(εH*W.card)+
      3*(2*((3*d:ℕ):ℝ))+2*deepCost i;
    0≤deep→
    ∀(ωout βout εstar ηpack ξreserve ζout p εout:ℝ),
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
    OrdinaryRootCoverSharpReferenceExists Ploc Gloc Floc Hloc I T B W (2+1) k (by decide)
      cover ell bin cin deep loss α ωout (βparent/2) βout (cweight*(1-δparent)^2)
      (B0/((ρ₀/16)*pstar^(2*(2+1)-1))) (2*hRef-ζparent) (δparent/2) (εparent+gap)
      εstar ηpack ξreserve ζout p εout fout binner crossout ∧
    0≤(∑t∈Jwin,cost t) ∧
    OrdinaryCleanupParentProfiles Ploc Gloc Floc Hloc ρi d I B pR pH (θhost+α-β/2)
      (εR*I.card) (εH*B.card) Ledit βe βh (fun u=>s (g u)) j raw ∧
    (∀v:I,|((Gloc.induce (I:Set _)).degree v:ℝ)-
      2*(Finset.univ.filter (fun u:B=>Hloc v.val u.val)).card|≤η*I.card) ∧
    Ledit≤rateParent*Fintype.card (markedVortexVertexType Q (i+1)) ∧
    OrdinaryFineWheelCoverResult 2 0 ξ aLoad Gloc Floc Hloc I T B W ∧
    (∀v,v∉I→|((Gloc.neighborFinset v∩I).card:ℝ)-2*(B.filter (Hloc v)).card|≤
      ηInitial*I.card+2*deepCost i) ∧
    (∀v,v∉T→|((Gloc.neighborFinset v∩T).card:ℝ)-2*(W.filter (Hloc v)).card|≤
      (initialIndexDensity U D*pH)*β*T.card+εR*T.card+2*(εH*W.card)+
        3*(2*((3*d:ℕ):ℝ))+2*deepCost i) ∧
    Nonempty (OrdinaryMixedHubWeightsInnerScale 2 bPair Bweight ηf Gloc Floc Hloc I B):=by
  intro V U Γ Color _ _ _ _ _ _ P Gbase G Hbase Hs D m hGbase hreg hn hD hρlo hρhi hmB hmC Q π hπ σ coins j s Kres cost deepCost i hi
    A pR pH θhost εR εH βe βh αcut pstar f g I T B W ρi Ploc Floc Gloc Hloc raw F R J S H S₀ H₀ X Tdeep Z Wdeep Jwin Ledit
    ηf bPair Bweight capHub hζcap
    hpRlo hpRhi hpHlo hpHhi hθhost hdegree hpEq hs hεR0 hεR hεRsample hεH0 hεH hεHsample hβe0 hβe hβh0 hβh hPairRim hPairSpoke havoid htrace hstate L hiL hρpos hβ0 hβ1 hεpos hm0 inner cross huniform hcost hmI hεRinitial hεHinitial hηInitial hbal hdiv hpH hcut hhref
    k hk βH ηH B0 βparent εparent ζparent gap lam hRef δparent cweight N₀ hB0 hρ₀ hpstar hζparent hN₀ hscale hroot hN
    βP ηP εTri weight hαcut hpminEq hsample hpRstar hpHstar hcweight hsize hξ0 haLoad0 hη0
    bin cin deep hdeep0 ωout βout εstar ηpack ξreserve ζout p εout ell cover loss fout binner crossout Aroot Croot Xf Zf
    hstatic hscaleV hscaleU
  dsimp only [OrdinaryTriangleSelectedSampleLevelDataGeneral] at hsample
  obtain ⟨hfamily,hdeep,hgood,hgood2,hrim0,heventParent,hcutsParent,hinputs,hweight⟩:=hsample
  have hrim:OrdinaryInducedRimCutEvent (Q.extendedVertices (i+2))
      (sampledOrientation (rawWheelGraph P σ) coins) αcut pstar:=by
    rw [hαcut,←hpminEq]
    simpa [Nat.add_assoc] using hrim0
  obtain ⟨hwin0,hwinI,hwinB,hprofile,hnearProfile,hmarginProfile,hLinner,hLparent⟩:=
    hbalance V U Γ Color P Gbase Hbase D m hreg hn hD hρlo hρhi hmB Q π hπ s j σ
      pR pH θhost εR εH βe βh hpRlo hpRhi hpHlo hθhost hdegree hpEq hs hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh
      Kres hPairRim hPairSpoke havoid hgood cost deepCost i hi A G Hs htrace hstate hcost
  have hboth:=ordinary_vortex_actual_uniform_two_step_balance_from_initial ε ρ₀ α pmin hmin ηInitial cBoundary δInitial d β mInitial hInitialAt
    P Gbase G Hbase Hs D m hreg hn hD hρlo hρhi hmI Q π hπ pR pH θhost εR εH βe βh s j σ Kres
    hpRlo hpRhi hpHlo hθhost hdegree hεR0 hεRinitial hεH0 hεHinitial hβe0 hβe hβh0 hβh hpEq hs hPairRim hPairSpoke havoid hgood
    (2+1) i L hi hiL cost deepCost A inner cross huniform hstate
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
  have hLcap:Ledit≤capHub*I.card:=hLinner.trans (mul_le_mul_of_nonneg_right hζcap (by positivity))
  have hevent:=hfamily (i+1) hi Ledit hL0 hLcap
  have hh:=hcover V U Γ Color P Gbase G Hbase Hs D m hGbase hreg hn hD hρlo hρhi hmC Q π hπ σ coins j s Kres cost deepCost i hi
    A pR pH (θhost+α-β/2) εR εH Ledit βe βh αcut pstar θhost α hpHlo hεRsample hεHsample hLcover
    hprofile rfl hεR0 hεH0 hdegree hpEq hgood hnear htrace hstate hbal hdiv hdeep hrim hpH hpHhi hεcut hζcut hζlimit hL0 hcut hhref
  have hdeepBal:=ordinary_vortex_actual_uniform_two_step_deep_balance P Gbase Hbase D m β ε pR pH εR εH Q π hπ d s j σ Kres
    hn hreg hρpos hβ0 hpH.le hεR0 hεH0 hpEq hPairRim hPairSpoke havoid hgood2 (2+1) i L hi hiL cost deepCost A G Hs inner cross huniform hstate
  have hS₀:S₀≤P:=sdiff_le.trans hGbase
  have hG:G≤P:=(ordinary_protected_trace_host_le S₀ G H₀ Hs X Tdeep Z Wdeep cost deepCost (i+1) A htrace hstate).trans hS₀
  have hlocal:Gloc≤Ploc:=by intro x y hxy;exact hG hxy
  have hweights:=hevent Gloc Hloc (by convert hprofile using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hlocal
  have hcost_i:0≤cost i:=by
    have hiwin:i∈Jwin:=by simp [Jwin]
    exact (hcost i hiwin).1
  have hLrate':2*((3*d:ℕ):ℝ)+cost i≤rateParent*Fintype.card (markedVortexVertexType Q (i+1)):=by
    simpa [Ledit,Jwin] using hLrate
  have hTX:T⊆I:=(ordinary_vortex_buffered_nested Q (i+1) 2 (by omega)).2.2.1
  have hWZ:W⊆B:=(ordinary_vortex_buffered_nested Q (i+1) 2 (by omega)).2.2.2
  have hbin:0≤bin:=by dsimp [bin];positivity
  have hinner:=ordinary_induced_balance_to_spanning Gloc Hloc I B bin hbin hnear
  have hBundle:=ordinary_protected_pair_trace_hub_balance 2 P Gbase Hbase D m β ε Q π hπ d s j σ
    Kres (Q.extendedVertices 1) (by rfl) hGbase hPairRim pR pH (θhost+α-β/2) εR εH βe βh bPair Bweight ηf capHub hfamily
    cost deepCost i hi A G Hs Ledit hL0 hLcap htrace hstate hbal hdiv
    (by convert hprofile using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
  obtain ⟨hhost,_hevent,_hhub,hlocalBal,hlocalDiv⟩:=hBundle
  have hFdegree:∀v,(F.degree v:ℝ)≤2*((3*d:ℕ):ℝ):=by
    intro v
    exact_mod_cast permutationConflictGraph_degree_le π (3*d) v
  have hphysical:=ordinary_protected_pair_trace_physical_edit P Gbase F Hbase D m β ε Q π hπ d j σ Kres
    (Q.extendedVertices 1) (Q.extendedIndices 1) (by rfl) (by rfl) hPairRim hPairSpoke havoid
    (2*((3*d:ℕ):ℝ)) (by positivity) hFdegree cost deepCost i 2 (by omega) hi A G Hs htrace hstate
  have hRefResult:=ordinary_vortex_local_triangle_fine_sharp_reference_separate_cross 2 (by omega)
    βH ηH B0 ρ₀ pstar βparent εparent ζparent rateParent N₀ hB0 hρ₀ hpstar hζparent hN₀ hscale
    k hk α cweight hRef δparent gap lam hroot P G Hs D m β ε Q (i+1) hi π hπ d j σ coins s
    βP ηP εTri pR pH η cin Ledit weight hreg hn hD hρlo hρhi hβ0 hβ1 hεpos hm0 hN hL0 hLrate
    (by convert hhost using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    (by convert hlocalBal using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    (by convert hlocalDiv using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    (by convert hinputs using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    hpRstar hpRhi hpHstar hpHhi hcweight hweight
    (by convert heventParent using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    (by convert hcutsParent using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    (by intro z;convert hphysical z using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    hη0 (by intro v;convert hnear v using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    (by intro v hv;convert hboth.2 v hv using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    ξ aLoad bin cin deep ωout βout εstar ηpack ξreserve ζout p εout
    hsize hξ0 haLoad0 hbin hdeep0 (by dsimp [bin];rfl) le_rfl hh
    (by intro v hv;convert hdeepBal v hv using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    (by convert hstatic using 1 <;> congr! 10 <;> first | exact Subsingleton.elim _ _ | (ext x;simp))
    (by simpa only [ell, Aroot, Croot, Nat.cast_zero, Nat.cast_ofNat] using hscaleV)
    (by simpa only [ell, Aroot, Croot, Nat.cast_zero, Nat.cast_ofNat] using hscaleU)
  refine ⟨?_,hwin0,?_,?_,hLrate,?_,?_,?_,?_⟩
  · convert hRefResult using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · convert hprofile using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro v;convert hnear v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro v hv
    convert hboth.2 v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro v hv
    convert hdeepBal v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · convert hweights using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
