module

public import Oberwolfach.OrdinaryTriangleHubAttachedProbability
public import Oberwolfach.OrdinaryAssignedCorrectionNamedProbability
public import Oberwolfach.OrdinaryDeepReservedOriginalHostBounds
public import Oberwolfach.OrdinaryFirstVortexCorrectionPointShape

@[expose] public section
/-! Attach triangle fine cover, rows and cuts to the original matching and
correction event on the same assigned sample and the same reference coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option diagnostics true
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_original_triangle_hub_same_sample
    (n qCount D mMatch d K mv mAbs aAbs bAbs q₀ Nc Ng Nh Ncol v₀:ℕ) (hd:2≤d)
    (βfreq ρ₀ α θ θhost lam aRow γ lamList ζDel tMatch ξMatch bMatch σ ζ χpair χlist χbal χbd χnbr χpairR χpath aEvent ε εabs εv βv ξAbs χlocal χglobal χhub χcol:ℝ)
    (κ aLoad ξdeep b Bweight ηHub δcap χdeep χHub εR εH χone χtwo χcut:ℝ)
    (htri:OrdinaryTriangleHubAfterSpacing d v₀ hd (α/2) ρ₀ (ρ₀*(βfreq/200)/2) κ aLoad ε ξdeep b Bweight ηHub δcap εR εH χdeep χHub χone χtwo χcut βv)
    (hn:0<n) (hmv:v₀≤mv) (hα:0<α) (hρ:0<ρ₀) (hβ:0<βfreq) (hθ:(1/2:ℝ)≤θhost)
    (F:Fin qCount→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (habundance:∀u,βfreq*n≤((Finset.univ.filter (fun v=>Fintype.card ((F u).connectedComponentMk v)=3)).card:ℝ))
    (hthreshold:∀u v,cycleThreshold (Fintype.card ((F u).connectedComponentMk v))≤θhost)
    (P:SimpleGraph (Fin n)) (hreg:P.IsRegularOfDegree D) (hdegree:(θhost+α)*(n:ℝ)≤D)
    (hρlo:ρ₀ ≤ initialIndexDensity (Fin qCount) D) (hρhi:initialIndexDensity (Fin qCount) D≤1)
    (π:Equiv.Perm (Fin n)) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (Q:Vortex (Fin qCount) P D βv ε mv) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (i₀:Fin K) (rsv:ℝ) (Cres:∀u,Finset (F u).ConnectedComponent)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((mMatch:ℝ)+1) ρ₀ (βfreq/200) d)
    (w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ)
    (seed:(Fin (mMatch+1)→Fin n)→ℝ)
    (hgeom:OrdinaryFirstVortexCorrectionPointShape n qCount D K mv d 3 Nc Ng Nh Ncol
      θhost α ρ₀ βfreq ε εabs εv P F hF i₀ rsv θ ((mMatch:ℝ)+1) βv Q)
    (density tR tH βe βh:ℕ→ℝ)
    (R:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)→Type)
    [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ))
    (hprior:OrdinaryAssignedCorrectionProbabilityShape 3 d mAbs aAbs bAbs (2*mv) q₀ n qCount K D hd
      (θ/2) χlocal χglobal χhub χcol ξAbs P (permutationConflictGraph π (3*d)) π F hF i₀ rsv θ ρ₀ (βfreq/200) mMatch sampling
      (Finset.univ\Q.extendedVertices 1) (Q.extendedVertices 1) (Q.extendedVertices Q.length)
      (Q.extendedIndices Q.length) (Q.extendedIndices 1) (Q.extendedIndices 1)
      R ρ ζ χpair χlist χbal χbd χnbr χpairR χpath Cres lam aRow γ σ aEvent ζDel lamList bMatch w seed tMatch ξMatch):
    let p:=initialIndexDensity (Fin qCount) D*rsv/2
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ ((mMatch:ℝ)+1) D
    let q:=ordinaryAssignedMarkedProbability F hF K θ ((mMatch:ℝ)+1)
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ ((mMatch:ℝ)+1)
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p 0 p₂ 0 sampling.u
      sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum d hd q sampling.hq sampling.hQ s sampling.hs sampling.hS)
    let E:=OrdinaryAssignedCorrectionEvent 3 d mAbs aAbs bAbs (2*mv) q₀ n qCount K D hd
      (θ/2) χlocal χglobal χhub χcol ξAbs P (permutationConflictGraph π (3*d)) π F hF i₀ rsv θ ρ₀ (βfreq/200) mMatch sampling
      (Finset.univ\Q.extendedVertices 1) (Q.extendedVertices 1) (Q.extendedVertices Q.length)
      (Q.extendedIndices Q.length) (Q.extendedIndices 1) (Q.extendedIndices 1)
      R ρ ζ χpair χlist χbal χbd χnbr χpairR χpath Cres lam aRow γ σ aEvent ζDel lamList bMatch w seed tMatch ξMatch
    let loss0:=(((((((0+3*ζ+χpair)+2*χlist)+χbal)+χbd)+χnbr)+χpairR)+χpath)
    let loss:=loss0+χcol+χhub+χglobal+2/(n:ℝ)^q₀+(1/(n:ℝ)+2/(n:ℝ)^2)+χlocal;
    OrdinaryTriangleHubAttachedProbability n qCount D mv d βv ε (α/2) κ aLoad p rsv (ρ₀*(βfreq/200)/2) εR εH δcap b Bweight ηHub
      P Q π hπ density tR tH βe βh s false R μ ρ E loss χdeep χHub χone χtwo χcut :=by
  intro p p₂ q s μ E loss0 loss
  obtain ⟨⟨hs,hp,hp1,hω,hD,hmargin,hωn,hp2,hp2r,hpres,hrsv1,hpeq,hspoke,hmarked⟩,hlocal⟩:=hgeom
  obtain ⟨hcycle,hdegree'⟩:=ordinary_deep_reserved_original_host_bounds n D qCount 3 θhost α ρ₀ βfreq
    (by omega) hn hα hρ hβ hρlo F hthreshold habundance hdegree
  have hcall:=htri (Fin n) (Fin qCount) Bool Bool
  have hFin:(fun (x y:Fin n)=>Classical.propDecidable (x=y))=instDecidableEqFin n:=Subsingleton.elim _ _
  rw [hFin] at hcall
  have hFinQ:(fun (x y:Fin qCount)=>Classical.propDecidable (x=y))=instDecidableEqFin qCount:=Subsingleton.elim _ _
  rw [hFinQ] at hcall
  have hpriorNamed:=ordinary_assigned_correction_named_probability 3 d mAbs aAbs bAbs (2*mv) q₀ n qCount K D hd
    (θ/2) χlocal χglobal χhub χcol ξAbs P (permutationConflictGraph π (3*d)) π F hF i₀ rsv θ ρ₀ (βfreq/200) mMatch sampling
    (Finset.univ\Q.extendedVertices 1) (Q.extendedVertices 1) (Q.extendedVertices Q.length)
    (Q.extendedIndices Q.length) (Q.extendedIndices 1) (Q.extendedIndices 1)
    R ρ ζ χpair χlist χbal χbd χnbr χpairR χpath Cres lam aRow γ σ aEvent ζDel lamList bMatch w seed tMatch ξMatch hprior
  have hpriorLoss:1-loss≤((μ.sigma ρ).prod (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.fairCoin))).probability E:=by
    dsimp only [loss,loss0]
    linarith only [hpriorNamed]
  exact hcall P D mv hreg (by simpa using hn) hρlo hρhi hmv Q π hπ hnoshort θhost hθ (by simpa using hcycle)
    (by simpa using hdegree') p 0 p₂ 0 sampling.u sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum
    rsv hp2r hpres hrsv1 hpeq density tR tH βe βh q sampling.hq sampling.hQ s sampling.hs sampling.hS false hspoke ρ E loss hpriorLoss
end Oberwolfach
