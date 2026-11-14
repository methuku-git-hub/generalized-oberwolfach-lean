module

public import Oberwolfach.OrdinaryVortexFullParentSelectionFromBundle

@[expose] public section
/-! Apply the preselected all-domain triangle event to the full parents of
the actual regular-host vortex, choosing weights before the raw sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_full_parent_selection_from_original
    (mWheel k d M:ℕ) (hm:3≤mWheel) (hd:2≤d) (α ρ₀ pstar βP ηP row ηH βH c B εTri ε χ:ℝ)
    (hpstar:0<pstar)
    (hselector:OrdinaryGeneralFixedDomainSelector mWheel k d M hm hd (max (1/2) (cycleThreshold (mWheel+1))) α pstar
      (ρ₀/16) βP ηP row ηH βH c B εTri ε χ (2*(3*d)) hpstar)
    (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (D vsize:ℕ) (β:ℝ) (Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hα:0<α) (hdegree:(max (1/2) (cycleThreshold (mWheel+1))+2*α)*Fintype.card V≤D)
    (hρ₀:0<ρ₀) (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hβ:0≤β) (hβα:β≤α/4) (hβ1:β≤1/4) (hβε:β≤εTri)
    (hε:0<ε) (hε1:ε≤1) (hερ:ε≤ρ₀/16) (hvsize:0<vsize)
    (hnoshort:∀x t,0<t→t<2*d+1→(π^t) x≠x)
    (pR pH:ℝ) (hpR:pstar≤pR) (hpR1:pR≤1) (hpH:pstar≤pH) (hpH1:pH≤1)
    (hpEq:pR=initialIndexDensity U D*pH)
    (L:ℕ) (hL:L<Q.length) (hM:(M:ℝ)≤ε*vsize/2):
    let W:=markedVortexVertexType Q;let Z:=markedVortexHubType Q;
    let f:=fun i=>(markedVortexVertexEmbedding Q i).toEmbedding;
    let g:=fun i=>markedVortexHubEmbedding Q i;
    let ρ:=markedVortexPermutation Q π hπ;
    let F:=permutationConflictGraph π (3*d);
    Nonempty (OrdinaryGeneralFullDomainSelection mWheel k d hm hd
      (max (1/2) (cycleThreshold (mWheel+1))) α pstar (ρ₀/16) βP ηP row ηH βH c B εTri χ (2*(3*d)) hpstar
      V U Γ Color W Z P F f g ρ L) :=by
  intro W Z f g ρ F
  have hinputs:=ordinary_vortex_general_parent_input_bundle_from_original mWheel (by omega) P D vsize d β ε α ρ₀
    pstar εTri pR pH Q π hπ hreg hn hα hdegree hρ₀ hρlo hρhi hβ hβα hβ1 hβε hε hε1 hερ hvsize
    hnoshort hpR hpR1 hpH hpH1 hpEq L M hL hM
  exact ordinary_vortex_full_parent_selection_from_bundle mWheel k d M hm hd α ρ₀ pstar βP ηP row ηH βH c B εTri ε χ
    hpstar hselector V U Γ Color P D vsize β Q π hπ pR pH hpR hpR1 hpH hpH1 L hinputs
end Oberwolfach
