module

public import Oberwolfach.OrdinaryParentReservedOriginalHostBounds
public import Oberwolfach.OrdinaryFirstVortexCorrectionPointShape
public import Oberwolfach.OrdinaryVortexGeneralParentInputsFromOriginal

@[expose] public section
/-! Choose full-parent weights for the actual assigned law, deriving the
parent host and probability inputs from the original factor assumptions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_original_parent_level_inputs
    (n qCount D rstar mMatch d K mv Nc Ng Nh Ncol:ℕ) (hd:2≤d) (hr:3≤rstar)
    (βfreq ρ₀ α θ θhost ε εabs εv βv εTri:ℝ)
    (hρ:0<ρ₀) (hβfreq:0<βfreq)
    (hn:0<n) (hmv:0<mv) (hα:0<α) (hθ:(1/2:ℝ)≤θhost)
    (hε:0<ε) (hε1:ε≤1) (hερ:ε≤ρ₀/16)
    (hβ:0≤βv) (hβ1:βv≤1/4) (hβα:βv≤α/8) (hβε:βv≤εTri)
    (F:Fin qCount→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (habundance:∀u,βfreq*n≤((Finset.univ.filter (fun v=>Fintype.card ((F u).connectedComponentMk v)=rstar)).card:ℝ))
    (hthreshold:∀u v,cycleThreshold (Fintype.card ((F u).connectedComponentMk v))≤θhost)
    (P:SimpleGraph (Fin n)) (hreg:P.IsRegularOfDegree D) (hdegree:(θhost+α)*(n:ℝ)≤D)
    (hρlo:ρ₀ ≤ initialIndexDensity (Fin qCount) D) (hρhi:initialIndexDensity (Fin qCount) D≤1)
    (π:Equiv.Perm (Fin n)) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (Q:Vortex (Fin qCount) P D βv ε mv) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (i₀:Fin K) (rsv:ℝ)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((mMatch:ℝ)+1) ρ₀ (βfreq/200) d)
    (hgeom:OrdinaryFirstVortexCorrectionPointShape n qCount D K mv d rstar Nc Ng Nh Ncol
      θhost α ρ₀ βfreq ε εabs εv P F hF i₀ rsv θ ((mMatch:ℝ)+1) βv Q)
    :
    let W:=markedVortexVertexType Q;let Z:=markedVortexHubType Q;
    let f:=fun i=>(markedVortexVertexEmbedding Q i).toEmbedding;
    let g:=fun i=>markedVortexHubEmbedding Q i;
    let ρ:=markedVortexPermutation Q π hπ;let Fconf:=permutationConflictGraph π (3*d);
    let L:=Q.length-1;
    ∀i,i<Q.length→OrdinaryDeepCoverLevelInputs (rstar-1) (2*(3*d)) d (α/2) (ρ₀*(βfreq/200)/2) (ρ₀/16) 1 εTri
      (P.comap (f i)) (Fconf.comap (f i)) (ρ i) (markedVortexInnerHubs Q i)
      (2*(initialIndexDensity (Fin qCount) D*rsv/2)) rsv
      (2*(Fintype.card (Z i):ℝ)/initialIndexDensity (Fin qCount) D) βv :=by
  intro W Z f g ρ Fconf L
  obtain ⟨⟨hs,hp,hp1,hω,hD,hmargin,hωn,hp2,hp2r,hpres,hrsv1,hpeq,hspoke,hmarked⟩,hlocal⟩:=hgeom
  let p:=initialIndexDensity (Fin qCount) D*rsv/2
  let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ ((mMatch:ℝ)+1) D
  have hsum:2*p+2*0+2*p₂+2*0+sampling.u≤1:=sampling.hsum
  have hp₂:0≤p₂:=sampling.hp₂
  have hu:0≤sampling.u:=sampling.hu
  have hpR1:2*p≤1:=by linarith
  have hparent:=ordinary_parent_reserved_original_host_bounds n D qCount rstar θhost α ρ₀ βfreq
    hr hn hα hρ hβfreq hθ hρlo F hthreshold habundance hdegree
  have hL:L<Q.length:=by dsimp [L]; have h:=Q.length_pos; omega
  have hM:(0:ℝ)≤ε*(mv:ℝ)/2:=by positivity
  have hinputs:=ordinary_vortex_general_parent_inputs_from_original (rstar-1) (by omega) P D mv d βv ε (α/2) ρ₀ (ρ₀*(βfreq/200)/2) εTri (2*p) rsv
    Q π hπ hreg (by simpa using hn) (by positivity) (by simpa using hparent) hρ hρlo hρhi hβ (by linarith) hβ1 hβε hε hε1 hερ hmv hnoshort
    hp2r hpR1 hpres hrsv1 hpeq L 0 hL (by simpa using hM)
  intro i hi
  exact hinputs.1 i (by dsimp [L]; omega)
end Oberwolfach
