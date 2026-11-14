module

public import Oberwolfach.OrdinaryOriginalTriangleHubVortexWitness
public import Oberwolfach.OrdinaryOriginalTriangleParentAttachPrior
public import Oberwolfach.OrdinaryTriangleHubProductEvent
public import Oberwolfach.OrdinaryOriginalTriangleHubSameSample

@[expose] public section
/-! Choose the original selector witnesses once and retain triangle cover,
row and cut tests on the same corrected matching sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_original_triangle_hub_parent_vortex_witness
    (n qCount D m k d K mv mAbs aAbs bAbs q₀ Nsel Ncorr Nc Ng Nh Ncol Ngeom:ℕ) (hd:2≤d)
    (βfreq ρ₀ α θ θhost lam aRow γ cap lamList ζDel τ tMatch ξMatch bMatch σ ζ χpair χlist χbal χbd χnbr χpairR χpath aEvent ε εabs εv βv ξAbs χlocal χglobal χhub χcol:ℝ)
    (BO:Fin K→ℝ)
    (hsel:OrdinaryOriginalThresholdForAllFactors 3 m k d K hd Nsel βfreq ρ₀ α θ θhost
      lam aRow γ cap lamList ζDel (βfreq/200) τ tMatch ξMatch bMatch BO ζ χpair χlist σ χbal χbd χnbr χpairR χpath aEvent)
    (hgeom:OrdinaryFirstVortexCorrectionThresholdShape Ngeom Nc Ng Nh Ncol θhost α ρ₀ βfreq ε εabs εv)
    (hcorr:OrdinaryWeightedCorrectionAfterLocalThresholds 3 d hd mAbs aAbs bAbs (2*mv) mv q₀ Ncorr Nc Ng Nh Ncol
      (α/2) (ρ₀*(βfreq/200)/2) (ρ₀/4) εabs εv (2*((3*d:ℕ):ℝ)) ξAbs (θ/2) χlocal χglobal χhub χcol (2/ε))
    (hnsel:Nsel≤n) (hngeom:Ngeom≤n) (hncorr:Ncorr≤n) (hn:2≤n) (hq:qCount≤n) (hmv:0<mv)
    (hρ:0<ρ₀) (he:0<ε)
    (F:Fin qCount→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (habundance:∀u,βfreq*n≤((Finset.univ.filter (fun v=>Fintype.card ((F u).connectedComponentMk v)=3)).card:ℝ))
    (hρlo:ρ₀ ≤ initialIndexDensity (Fin qCount) D) (hρhi:initialIndexDensity (Fin qCount) D≤1)
    (hthreshold:∀u v,cycleThreshold (Fintype.card ((F u).connectedComponentMk v))≤θhost)
    (P:SimpleGraph (Fin n)) (hreg:P.IsRegularOfDegree D) (π:Equiv.Perm (Fin n))
    (hdegree:(θhost+α)*(n:ℝ)≤D) (hθ:(1/2:ℝ)≤θhost) (hα:0<α)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (Q:Vortex (Fin qCount) P D βv ε mv) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i) (hβv:0≤βv) (hβv1:βv≤1/4)
    (v₀:ℕ) (κ aLoad ξdeep b Bweight ηHub δcap χdeep χHub εR εH χone χtwo χcut:ℝ)
    (htri:OrdinaryTriangleHubAfterSpacing d v₀ hd (α/2) ρ₀ (ρ₀*(βfreq/200)/2) κ aLoad ε ξdeep b Bweight ηHub δcap εR εH χdeep χHub χone χtwo χcut βv)
    (hβfreq:0<βfreq) (hdeepSize:v₀≤mv) (density tR tH βe βh:ℕ→ℝ)
    (kParent Mhost Mcut:ℕ) (βP ηP ηH βH cParent Bparent εTri χhost δref href χref:ℝ)
    (hpstar:0<ρ₀*(βfreq/200)/2)
    (hselector:OrdinaryTriangleFixedDomainSelector kParent d Mhost hd (max (1/2) (cycleThreshold 3))
      (α/2) (ρ₀*(βfreq/200)/2) (ρ₀/16) βP ηP ηH βH cParent Bparent εTri ε χhost (2*(3*d)) hpstar)
    (hcuts:OrdinaryReferenceCutsDomainSelector d Mcut hd (α/2) (ρ₀*(βfreq/200)/2)
      (ρ₀/16) δref href ε χref (2*(3*d)))
    (hε1:ε≤1) (hερ:ε≤ρ₀/16) (hβα:βv≤α/8) (hβε:βv≤εTri)
    (hM:(Mhost:ℝ)≤ε*mv/2) (hMcut:(Mcut:ℝ)≤ε*mv/2):
    ∃(i₀:Fin K) (rsv:ℝ) (Cres:∀u,Finset (F u).ConnectedComponent)
      (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((m:ℝ)+1) ρ₀ (βfreq/200) d)
      (w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ)
      (seed:(Fin (m+1)→Fin n)→ℝ),
      OrdinaryOriginalSelectorFactorWitness n qCount D 3 m k d K hd
        ρ₀ θ lam aRow γ lamList ζDel (βfreq/200) τ tMatch ξMatch bMatch σ ζ χpair χlist χbal χbd χnbr χpairR χpath aEvent α
        BO F hF P π i₀ rsv Cres sampling w seed ∧
      OrdinaryFirstVortexCorrectionPointShape n qCount D K mv d 3 Nc Ng Nh Ncol
        θhost α ρ₀ βfreq ε εabs εv P F hF i₀ rsv θ ((m:ℝ)+1) βv Q ∧
      ∃selection:OrdinaryTriangleFullDomainSelection kParent d hd (max (1/2) (cycleThreshold 3))
        (α/2) (ρ₀*(βfreq/200)/2) (ρ₀/16) βP ηP ηH βH cParent Bparent εTri χhost (2*(3*d)) hpstar
        (Fin n) (Fin qCount) Bool Bool (markedVortexVertexType Q) (markedVortexHubType Q)
        P (permutationConflictGraph π (3*d)) (fun i=>(markedVortexVertexEmbedding Q i).toEmbedding)
        (fun i=>markedVortexHubEmbedding Q i) (markedVortexPermutation Q π hπ) (Q.length-1),
      ∀{R:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)→Type}
      [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ)),
    let p:=initialIndexDensity (Fin qCount) D*rsv/2
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ ((m:ℝ)+1) D
    let q:=ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1)
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ ((m:ℝ)+1)
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p 0 p₂ 0 sampling.u
      sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum d hd q sampling.hq sampling.hQ s sampling.hs sampling.hS)
    let E:=OrdinaryAssignedCorrectionEvent 3 d mAbs aAbs bAbs (2*mv) q₀ n qCount K D hd
      (θ/2) χlocal χglobal χhub χcol ξAbs P (permutationConflictGraph π (3*d)) π F hF i₀ rsv θ ρ₀ (βfreq/200) m sampling
      (Finset.univ\Q.extendedVertices 1) (Q.extendedVertices 1) (Q.extendedVertices Q.length)
      (Q.extendedIndices Q.length) (Q.extendedIndices 1) (Q.extendedIndices 1)
      R ρ ζ χpair χlist χbal χbd χnbr χpairR χpath Cres lam aRow γ σ aEvent ζDel lamList bMatch w seed tMatch ξMatch
    let loss0:=(((((((0+3*ζ+χpair)+2*χlist)+χbal)+χbd)+χnbr)+χpairR)+χpath)
    let loss:=loss0+χcol+χhub+χglobal+2/(n:ℝ)^q₀+(1/(n:ℝ)+2/(n:ℝ)^2)+χlocal;
    let Good:=OrdinaryTriangleHubProductEvent n qCount D mv d βv ε (α/2) κ aLoad p rsv (ρ₀*(βfreq/200)/2) εR εH δcap b Bweight ηHub
      P Q π hπ density tR tH βe βh s false R μ ρ E loss χdeep χHub χone χtwo χcut;
    let All:=OrdinaryTriangleParentProductEvent n qCount D mv kParent d (Q.length-1) hd βv ε (α/2)
      (ρ₀*(βfreq/200)/2) βP ηP ηH βH cParent Bparent δref href P Q π hπ selection.weight p rsv s false R Good;
    1-(loss+χdeep+χone+χtwo+χcut+χHub)-χhost-χref≤
      ((μ.sigma ρ).prod (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.fairCoin))).probability All :=by
  obtain ⟨i₀,rsv,Cres,sampling,w,seed,hwitness,hpoint,htriPrior⟩:=
    ordinary_original_triangle_hub_vortex_witness n qCount D m k d K mv mAbs aAbs bAbs q₀ Nsel Ncorr Nc Ng Nh Ncol Ngeom hd
      βfreq ρ₀ α θ θhost lam aRow γ cap lamList ζDel τ tMatch ξMatch bMatch σ ζ χpair χlist χbal χbd χnbr χpairR χpath aEvent ε εabs εv βv ξAbs χlocal χglobal χhub χcol
      BO hsel hgeom hcorr hnsel hngeom hncorr hn hq hmv hρ he F hF habundance hρlo hρhi hthreshold P hreg π hdegree hθ hα hnoshort Q hπ hβv hβv1
      v₀ κ aLoad ξdeep b Bweight ηHub δcap χdeep χHub εR εH χone χtwo χcut htri hβfreq hdeepSize density tR tH βe βh
  obtain ⟨selection,hparent⟩:=ordinary_original_triangle_parent_attach_prior n qCount D m kParent d K mv Mhost Mcut Nc Ng Nh Ncol hd
      βfreq ρ₀ α θ θhost ε εabs εv βv βP ηP ηH βH cParent Bparent εTri χhost δref href χref hρ hβfreq hpstar hselector hcuts
      (by omega) hmv hα hθ he hε1 hερ hβv hβv1 hβα hβε F hF habundance hthreshold P hreg hdegree hρlo hρhi π hnoshort Q hπ
      i₀ rsv sampling hpoint hM hMcut
  refine ⟨i₀,rsv,Cres,sampling,w,seed,hwitness,hpoint,selection,?_⟩
  intro R inst ρ p p₂ q s μ E loss0 loss Good All
  have hbound:1-(loss+χdeep+χone+χtwo+χcut+χHub)≤
      ((μ.sigma ρ).prod (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.fairCoin))).probability Good:=htriPrior ρ
  exact hparent ρ Good (1-(loss+χdeep+χone+χtwo+χcut+χHub)) hbound
end Oberwolfach
