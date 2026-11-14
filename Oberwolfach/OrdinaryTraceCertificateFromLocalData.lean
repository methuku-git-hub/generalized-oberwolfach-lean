module

public import Oberwolfach.OrdinaryVortexTraceCertificateFromSharp
public import Oberwolfach.OrdinaryCertificateCommonSizeThreshold

@[expose] public section
/-! The protected-history sharp-reference bundle feeds the selected wheel
certificate, with its size and conflict budget supplied by one threshold. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 45000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_trace_certificate_from_local_data
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [LinearOrder U]
    (s:OrdinaryVortexFineCertificateParametersGeneralLoad) (hcert:OrdinaryVortexFineCertificateAtGeneralLoad s)
    (P Gbase G:SimpleGraph V) (Hbase Hs:V→U→Prop) (D mv:ℕ) (βv εv:ℝ)
    (Q:Vortex U P D βv εv mv) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i) (d:ℕ)
    (σ:RawWheelOutcome V U Γ Color) (K:Finset (Sym2 V⊕(V×U)))
    (hr:∀v∈Q.extendedVertices 1,∀w∈Q.extendedVertices 1,
      ((rawWheelGraph P σ)\permutationConflictGraph π (3*d)).Adj v w↔Gbase.Adj v w)
    (cost deepCost:ℕ→ℝ) (i:ℕ) (A:Finset (Sym2 V⊕(V×U)))
    (hready:OrdinaryVortexTraceCertificateFromSharpAt s hcert P Gbase Hbase D mv βv εv Q π hπ d σ K hr cost deepCost i A G Hs):
    let S:=Gbase\ordinaryResourceRim Gbase K;
    let H:=fun v u=>Hbase v u∧¬(Sum.inr (v,u)∈K);
    let X:=fun k=>Q.extendedVertices (k+1);let Tdeep:=fun k=>Q.extendedVertices (k+2);
    let Z:=fun k=>Q.extendedIndices (k+1);let Wdeep:=fun k=>Q.extendedIndices (k+2);
    let f:=markedVortexVertexEmbedding Q (i+1);let g:=markedVortexHubEmbedding Q (i+1);
    letI : DecidableEq (markedVortexVertexType Q (i+1)):=Classical.decEq _;
    letI : DecidableEq (markedVortexHubType Q (i+1)):=Classical.decEq _;
    let I:=markedVortexInnerVertices Q (i+1);let T:=ordinaryVortexBufferedVertices Q (i+1) 2;
    let B:=markedVortexInnerHubs Q (i+1);let W:=ordinaryVortexBufferedHubs Q (i+1) 2;
    let Ploc:=P.comap f;let Gloc:=G.comap f;let Floc:=(permutationConflictGraph π (3*d)).comap f;
    let Hloc:=fun v u=>Hs (f v) (g u);let ρi:=markedVortexPermutation Q π hπ (i+1);
    let raw:=ordinaryRawRestrictPair f g σ;
    ∀(ξroot aLoad lam bin cin deep βparent h εparent ξ ζ pR pH density Ledit ρ₀ εR εH eParent hParent:ℝ)
      (sp:markedVortexHubType Q (i+1)→Color→ℝ) (j:Color),
    let n:ℝ:=Fintype.card (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1));
    let cover:=10*ξroot*I.card;let loss:=12*aLoad*Fintype.card (markedVortexVertexType Q (i+1));
    let ell:=max (18*aLoad*Fintype.card (markedVortexVertexType Q (i+1))+3*((W.card:ℝ)+((s.loadK:ℝ)+1)*T.card))
      (3*aLoad*Fintype.card (markedVortexVertexType Q (i+1))*((s.m:ℝ)+1)+(T.card:ℝ)*((s.m:ℝ)+1));
    OrdinaryProtectedTrace S H X Tdeep Z Wdeep cost deepCost (i+1) A→ ordinaryHostResources G Hs=A→
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
    (∀u,(s.m+1)∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    (2*(3*d):ℕ)≤s.b₀→(2*((3*d:ℕ):ℝ))≤s.L→s.hpack≤h-ξ-ζ→
    OrdinaryCleanupParentProfiles Ploc Gloc Floc Hloc ρi d I B pR pH density (εR*I.card) (εH*B.card)
      Ledit (eParent*εv) (hParent*εv) sp j raw→
    Nonempty (OrdinaryMixedHubWeightsInnerScale s.m s.bHub s.BHub s.ηhub Gloc Floc Hloc I B)→
    OrdinaryVortexAsymmetricPairingGeometryAt Q (i+1) s.Ncert ρ₀ s.δend εR εH Ledit s.ζhub s.ζlocal s.γ eParent→
    (T.card:ℝ)≤(s.βe/4)*n→(W.card:ℝ)≤(s.βh/2)*n→
    (T.card:ℝ)+W.card≤lam*Fintype.card (markedVortexVertexType Q (i+1))→
    (∃Root:OrdinaryRootCoverNonrootData Gloc Floc Hloc I T B W (s.m+1) cover ell,
      Nonempty (OrdinaryRootCoverSharpReferenceData Ploc Gloc Floc Hloc I T B W (s.m+1) s.k (by have hm:=s.hm;omega)
        cover ell bin cin deep loss Root s.α s.ω βparent s.β s.bRoot s.BRoot h s.δ εparent s.εstar s.ηpack ξ ζ s.p s.εgeom
        (deep+2*cover) (bin+deep+4*cover) (cin+deep+loss)))→
    s.κ≤ρ₀/8→s.p₀≤pR→s.p₀≤pH→pH≤1→0≤εR→0≤εH→0≤Ledit→
    ∀(Nfinish M:ℕ) (rate θmatch ellCap finishCap kcap:ℝ),0<θmatch→
    θmatch≤(min (s.ζhub*s.γ*(1/4:ℝ)) (s.ζlocal*(1/4:ℝ))/2)*εv→
    s.εsup≤s.p^2/4→s.p≤4*θmatch→20*Real.sqrt (2*s.p)≤θmatch/2→
    0≤ξroot→0≤aLoad→0≤lam→lam≤1/4→
    max (max (max (4*s.n₀) (4*s.Nreserve)) (max s.Nclean 64)) (max s.Ncert Nfinish)≤M→M≤I.card→
    max (18*aLoad+3*(((s.loadK:ℝ)+1)*lam)) ((3*aLoad+lam)*((s.m:ℝ)+1))≤ellCap→10*ξroot≤finishCap→
    s.L≤kcap^2*M→
    OrdinaryAsymmetricFinishSchedule s.m Nfinish eParent hParent εv s.βe s.βh θmatch s.p s.δsample ellCap finishCap kcap rate s.ν s.cap→
    OrdinaryWheelLikelySeparateCostsCertificate Gloc Floc Hloc I T B W (s.m+1) (rate*n) cover :=by
  intro S H X Tdeep Z Wdeep f g I T B W Ploc Gloc Floc Hloc ρi raw ξroot aLoad lam bin cin deep βparent h εparent ξ ζ pR pH density Ledit ρ₀ εR εH eParent hParent sp j
    n cover loss ell htrace hstate hbal hdiv hb₀ hL hpack hprofile hweight hpair hT hW hTW hsharp hκ hpR hpH hpH1 hεR hεH hLedit
    Nfinish M rate θmatch ellCap finishCap kcap hθ hθcap hεsup hpθ hsqrt hξ ha hlam hlam1 hbase hM hell hcover hbudget hsched
  obtain ⟨hweight⟩:=hweight
  have hsize:=hbase.trans hM
  have hLsize:s.L≤kcap^2*n:=ordinary_certificate_budget_at_inner_size I M s.L kcap hM hbudget
  have hdecU:(fun (a b:U)=>Classical.propDecidable (a=b))=
      (LinearOrder.toDecidableEq:DecidableEq U):=Subsingleton.elim _ _
  have hBufferedEq:
      @ordinaryVortexBufferedHubs V U _ _ (fun a b=>Classical.propDecidable (a=b)) P D mv βv εv Q (i+1) 2 =
      @ordinaryVortexBufferedHubs V U _ _ (LinearOrder.toDecidableEq:DecidableEq U) P D mv βv εv Q (i+1) 2 :=by rw [hdecU]
  have hInnerEq:
      @markedVortexInnerHubs V U _ _ (fun a b=>Classical.propDecidable (a=b)) P D mv βv εv Q (i+1) =
      @markedVortexInnerHubs V U _ _ (LinearOrder.toDecidableEq:DecidableEq U) P D mv βv εv Q (i+1) :=by rw [hdecU]
  have hresult:=hready
    (by convert htrace using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    (by convert hstate using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    (by intro v;convert hbal v using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    (by intro u;convert hdiv u using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    hb₀ hL ξroot aLoad lam bin cin deep loss βparent h εparent ξ ζ
    (deep+2*cover) (bin+deep+4*cover) (cin+deep+loss) pR pH density Ledit ρ₀ εR εH eParent hParent sp j
    hpack (by
      try simp only [hBufferedEq] at hsharp ⊢
      convert hsharp using 1 <;> congr! 10 <;> first | rfl | simp | exact congrArg Finset.card hBufferedEq | exact congrArg Finset.card hBufferedEq.symm | exact Subsingleton.elim _ _) hT
    (by dsimp only [W,n] at hW;convert hW using 1 <;> congr! 10 <;> first | rfl | simp | exact congrArg Finset.card hBufferedEq | exact congrArg Finset.card hBufferedEq.symm | exact Subsingleton.elim _ _)
    (by
      try simp only [hInnerEq] at hprofile ⊢
      convert hprofile using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    hκ (by convert hpair using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _) hpR hpH hpH1 hεR hεH hLedit
    (by
      try simp only [hInnerEq] at hweight ⊢
      convert hweight using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    Nfinish rate θmatch ellCap finishCap kcap hθ hθcap hεsup hpθ hsqrt hξ ha hlam hlam1 hsize
    (by dsimp only [T,W] at hTW;convert hTW using 1 <;> congr! 10 <;> first | rfl | simp | exact congrArg Finset.card hBufferedEq | exact congrArg Finset.card hBufferedEq.symm | exact Subsingleton.elim _ _)
    hell hcover hLsize hsched
  dsimp only [Gloc,Floc,Hloc,I,T,B,W,f,g,n,cover]
  convert hresult using 1 <;> congr! 10 <;> first | rfl | exact hInnerEq | exact hInnerEq.symm | exact hBufferedEq | exact hBufferedEq.symm | simp | exact Subsingleton.elim _ _
end Oberwolfach
