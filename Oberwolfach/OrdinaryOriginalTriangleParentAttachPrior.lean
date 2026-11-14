module

public import Oberwolfach.OrdinaryOriginalTriangleParentSelection
public import Oberwolfach.OrdinaryTriangleParentProductEvent

@[expose] public section
/-! Choose parent weights once and attach the parent and reference tests to
any prior on the actual assigned sample and the same reference coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_original_triangle_parent_attach_prior
    (n qCount D mMatch kParent d K mv Mhost Mcut Nc Ng Nh Ncol:ℕ) (hd:2≤d)
    (βfreq ρ₀ α θ θhost ε εabs εv βv βP ηP ηH βH c B εTri χhost δref href χref:ℝ)
    (hρ:0<ρ₀) (hβfreq:0<βfreq) (hpstar:0<ρ₀*(βfreq/200)/2)
    (hselector:OrdinaryTriangleFixedDomainSelector kParent d Mhost hd
      (max (1/2) (cycleThreshold 3)) (α/2) (ρ₀*(βfreq/200)/2)
      (ρ₀/16) βP ηP ηH βH c B εTri ε χhost (2*(3*d)) hpstar)
    (hcuts:OrdinaryReferenceCutsDomainSelector d Mcut hd (α/2) (ρ₀*(βfreq/200)/2)
      (ρ₀/16) δref href ε χref (2*(3*d)))
    (hn:0<n) (hmv:0<mv) (hα:0<α) (hθ:(1/2:ℝ)≤θhost)
    (hε:0<ε) (hε1:ε≤1) (hερ:ε≤ρ₀/16)
    (hβ:0≤βv) (hβ1:βv≤1/4) (hβα:βv≤α/8) (hβε:βv≤εTri)
    (F:Fin qCount→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (habundance:∀u,βfreq*n≤((Finset.univ.filter (fun v=>Fintype.card ((F u).connectedComponentMk v)=3)).card:ℝ))
    (hthreshold:∀u v,cycleThreshold (Fintype.card ((F u).connectedComponentMk v))≤θhost)
    (P:SimpleGraph (Fin n)) (hreg:P.IsRegularOfDegree D) (hdegree:(θhost+α)*(n:ℝ)≤D)
    (hρlo:ρ₀ ≤ initialIndexDensity (Fin qCount) D) (hρhi:initialIndexDensity (Fin qCount) D≤1)
    (π:Equiv.Perm (Fin n)) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (Q:Vortex (Fin qCount) P D βv ε mv) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (i₀:Fin K) (rsv:ℝ)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((mMatch:ℝ)+1) ρ₀ (βfreq/200) d)
    (hgeom:OrdinaryFirstVortexCorrectionPointShape n qCount D K mv d 3 Nc Ng Nh Ncol
      θhost α ρ₀ βfreq ε εabs εv P F hF i₀ rsv θ ((mMatch:ℝ)+1) βv Q)
    (hM:(Mhost:ℝ)≤ε*mv/2) (hMcut:(Mcut:ℝ)≤ε*mv/2):
    let W:=markedVortexVertexType Q;let Z:=markedVortexHubType Q;
    let f:=fun i=>(markedVortexVertexEmbedding Q i).toEmbedding;
    let g:=fun i=>markedVortexHubEmbedding Q i;
    let ρi:=markedVortexPermutation Q π hπ;let Fconf:=permutationConflictGraph π (3*d);
    let L:=Q.length-1;
    ∃selection:OrdinaryTriangleFullDomainSelection kParent d hd
      (max (1/2) (cycleThreshold 3)) (α/2) (ρ₀*(βfreq/200)/2) (ρ₀/16)
      βP ηP ηH βH c B εTri χhost (2*(3*d)) hpstar (Fin n) (Fin qCount) Bool Bool W Z P Fconf f g ρi L,
    ∀{R:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)→Type}
      [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ))
      (Good:(Σσ,R σ)×(Sym2 (Fin n)→Bool)→Prop) (bound:ℝ),
    let p:=initialIndexDensity (Fin qCount) D*rsv/2
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ ((mMatch:ℝ)+1) D
    let q:=ordinaryAssignedMarkedProbability F hF K θ ((mMatch:ℝ)+1)
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ ((mMatch:ℝ)+1)
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p 0 p₂ 0 sampling.u
      sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum d hd q sampling.hq sampling.hQ s sampling.hs sampling.hS)
    let ν:=FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.fairCoin)
    let All:=OrdinaryTriangleParentProductEvent n qCount D mv kParent d L hd βv ε (α/2)
      (ρ₀*(βfreq/200)/2) βP ηP ηH βH c B δref href P Q π hπ selection.weight p rsv s false R Good;
    bound≤((μ.sigma ρ).prod ν).probability Good→
    bound-χhost-χref≤((μ.sigma ρ).prod ν).probability All :=by
  intro W Z f g ρi Fconf L
  obtain ⟨selection⟩:=ordinary_original_triangle_parent_selection n qCount D mMatch kParent d K mv Mhost Nc Ng Nh Ncol hd
    βfreq ρ₀ α θ θhost ε εabs εv βv βP ηP ηH βH c B εTri χhost hρ hβfreq hpstar hselector
    hn hmv hα hθ hε hε1 hερ hβ hβ1 hβα hβε F hF habundance hthreshold P hreg hdegree hρlo hρhi π hnoshort Q hπ
    i₀ rsv sampling hgeom hM
  refine ⟨selection,?_⟩
  intro R inst ρ Good bound p p₂ q s μ ν All hGood
  obtain ⟨⟨hs,hp,hp1,hω,hD,hmargin,hωn,hp2,hp2r,hpres,hrsv1,hpeq,hspoke,hmarked⟩,hlocal⟩:=hgeom
  have hparent:=ordinary_parent_reserved_original_host_bounds n D qCount 3 θhost α ρ₀ βfreq
    (by omega) hn hα hρ hβfreq hθ hρlo F hthreshold habundance hdegree
  have hL:L<Q.length:=by dsimp [L]; have h:=Q.length_pos; omega
  have hcall:=ordinary_expanded_vortex_triangle_parent_selection_common kParent d Mhost Mcut hd
    (α/2) ρ₀ (ρ₀*(βfreq/200)/2) βP ηP ηH βH c B εTri ε χhost δref href χref hpstar hcuts
    (Fin n) (Fin qCount) Bool Bool
  have hFin:(fun (x y:Fin n)=>Classical.propDecidable (x=y))=instDecidableEqFin n:=Subsingleton.elim _ _
  try rw [hFin] at hcall
  have hFinQ:(fun (x y:Fin qCount)=>Classical.propDecidable (x=y))=instDecidableEqFin qCount:=Subsingleton.elim _ _
  try rw [hFinQ] at hcall
  have h:=hcall P D mv βv Q π hπ hreg (by simpa using hn) (by positivity) (by simpa using hparent)
    hρ hρlo hρhi hβ (by linarith) hβ1 hβε hε hε1 hερ hmv hnoshort
    p 0 p₂ 0 sampling.u sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum
    rsv hp2r hpres hrsv1 hpeq L hL hM hMcut selection q sampling.hq sampling.hQ s sampling.hs sampling.hS false hspoke ρ Good (1-bound) (by linarith)
  change bound-χhost-χref≤((μ.sigma ρ).prod ν).probability All
  change 1-(1-bound)-χhost-χref≤((μ.sigma ρ).prod ν).probability All at h
  linarith only [h]
end Oberwolfach
