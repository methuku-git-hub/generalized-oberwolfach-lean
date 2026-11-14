module

public import Oberwolfach.OrdinaryDeepRowsCutsAttachedEvent
public import Oberwolfach.OrdinaryAssignedCorrectionNamedProbability
public import Oberwolfach.OrdinaryDeepReservedOriginalHostBounds
public import Oberwolfach.OrdinaryFirstVortexCorrectionPointShape

@[expose] public section
/-! Attach the non-triangle all-level event to the original matching and
correction event, on the same assigned sample and the same reference coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_original_deep_same_sample
    (n qCount D rstar mMatch d K mv mAbs aAbs bAbs q₀ Nc Ng Nh Ncol Kdeep v₀:ℕ) (hd:2≤d)
    (βfreq ρ₀ α θ θhost lam aRow γ lamList ζDel tMatch ξMatch bMatch σ ζ χpair χlist χbal χbd χnbr χpairR χpath aEvent ε εabs εv βv ξAbs χlocal χglobal χhub χcol:ℝ)
    (αcut c C a ε₀ ρdeep θdeep aLoad ξdeep b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut capDeep:ℝ)
    (hdeep:OrdinaryDeepRowsCutsAfterSpacing (rstar-1) Kdeep d hd v₀ βv
      (α/2) ρ₀ (ρ₀*(βfreq/200)/2) αcut c C a ε₀ ρdeep θdeep aLoad ε ξdeep b Bweight ηHub Kdom
      χinner χdeep eParent hParent εR εH χone χtwo χcut capDeep)
    (hr:3≤rstar) (hn:0<n) (hmv:v₀≤mv) (hα:0<α) (hρ:0<ρ₀) (hβ:0<βfreq) (hθ:(1/2:ℝ)≤θhost)
    (F:Fin qCount→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (habundance:∀u,βfreq*n≤((Finset.univ.filter (fun v=>Fintype.card ((F u).connectedComponentMk v)=rstar)).card:ℝ))
    (hthreshold:∀u v,cycleThreshold (Fintype.card ((F u).connectedComponentMk v))≤θhost)
    (P:SimpleGraph (Fin n)) (hreg:P.IsRegularOfDegree D) (hdegree:(θhost+α)*(n:ℝ)≤D)
    (hρlo:ρ₀ ≤ initialIndexDensity (Fin qCount) D) (hρhi:initialIndexDensity (Fin qCount) D≤1)
    (π:Equiv.Perm (Fin n)) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (Q:Vortex (Fin qCount) P D βv ε mv) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (i₀:Fin K) (rsv:ℝ) (Cres:∀u,Finset (F u).ConnectedComponent)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((mMatch:ℝ)+1) ρ₀ (βfreq/200) d)
    (w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ)
    (seed:(Fin (mMatch+1)→Fin n)→ℝ)
    (hgeom:OrdinaryFirstVortexCorrectionPointShape n qCount D K mv d rstar Nc Ng Nh Ncol
      θhost α ρ₀ βfreq ε εabs εv P F hF i₀ rsv θ ((mMatch:ℝ)+1) βv Q)
    (density tR tH:ℕ→ℝ)
    (R:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)→Type)
    [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ))
    (hprior:OrdinaryAssignedCorrectionProbabilityShape rstar d mAbs aAbs bAbs (2*mv) q₀ n qCount K D hd
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
    let E:=OrdinaryAssignedCorrectionEvent rstar d mAbs aAbs bAbs (2*mv) q₀ n qCount K D hd
      (θ/2) χlocal χglobal χhub χcol ξAbs P (permutationConflictGraph π (3*d)) π F hF i₀ rsv θ ρ₀ (βfreq/200) mMatch sampling
      (Finset.univ\Q.extendedVertices 1) (Q.extendedVertices 1) (Q.extendedVertices Q.length)
      (Q.extendedIndices Q.length) (Q.extendedIndices 1) (Q.extendedIndices 1)
      R ρ ζ χpair χlist χbal χbd χnbr χpairR χpath Cres lam aRow γ σ aEvent ζDel lamList bMatch w seed tMatch ξMatch
    let loss0:=(((((((0+3*ζ+χpair)+2*χlist)+χbal)+χbd)+χnbr)+χpairR)+χpath)
    let loss:=loss0+χcol+χhub+χglobal+2/(n:ℝ)^q₀+(1/(n:ℝ)+2/(n:ℝ)^2)+χlocal;
    OrdinaryDeepRowsCutsAttachedEvent n qCount D mv (rstar-1) Kdeep d βv ε P Q π hπ
      p rsv (ρ₀*(βfreq/200)/2) αcut c C b Bweight ξdeep ηHub Kdom a aLoad ρdeep θdeep capDeep eParent hParent εR εH
      density tR tH s false R μ ρ E loss χinner χdeep χone χtwo χcut :=by
  intro p p₂ q s μ E loss0 loss
  obtain ⟨⟨hs,hp,hp1,hω,hD,hmargin,hωn,hp2,hp2r,hpres,hrsv1,hpeq,hspoke,hmarked⟩,hlocal⟩:=hgeom
  obtain ⟨hcycle,hdegree'⟩:=ordinary_deep_reserved_original_host_bounds n D qCount rstar θhost α ρ₀ βfreq
    hr hn hα hρ hβ hρlo F hthreshold habundance hdegree
  have hcall:=hdeep (Fin n) (Fin qCount) Bool Bool
  have hFin:(fun (x y:Fin n)=>Classical.propDecidable (x=y))=instDecidableEqFin n:=Subsingleton.elim _ _
  rw [hFin] at hcall
  obtain ⟨weight,hweight,hall⟩:=hcall P D mv hreg (by simpa using hn)
    hρlo hρhi hmv Q π hπ hnoshort θhost p 0 p₂ 0 sampling.u hθ hcycle (by simpa using hdegree')
    sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum rsv hp2r hpres hrsv1 hpeq
  have hpriorNamed:=ordinary_assigned_correction_named_probability rstar d mAbs aAbs bAbs (2*mv) q₀ n qCount K D hd
    (θ/2) χlocal χglobal χhub χcol ξAbs P (permutationConflictGraph π (3*d)) π F hF i₀ rsv θ ρ₀ (βfreq/200) mMatch sampling
    (Finset.univ\Q.extendedVertices 1) (Q.extendedVertices 1) (Q.extendedVertices Q.length)
    (Q.extendedIndices Q.length) (Q.extendedIndices 1) (Q.extendedIndices 1)
    R ρ ζ χpair χlist χbal χbd χnbr χpairR χpath Cres lam aRow γ σ aEvent ζDel lamList bMatch w seed tMatch ξMatch hprior
  have hpriorLoss:1-loss≤((μ.sigma ρ).prod (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.fairCoin))).probability E:=by
    dsimp only [loss,loss0]
    linarith only [hpriorNamed]
  refine ⟨weight,hweight,?_⟩
  exact hall density tR tH q sampling.hq sampling.hQ s sampling.hs sampling.hS false hspoke ρ E loss hpriorLoss
end Oberwolfach
