module

public import Oberwolfach.OrdinaryTriangleFullDomainSelection
public import Oberwolfach.OrdinaryVortexGeneralParentInputBundle

@[expose] public section
/-! Select parent weights from the named vortex geometry bundle before
specializing the resulting probability callback. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_full_parent_triangle_selection_from_bundle
    (k d M:ℕ) (hd:2≤d) (α ρ₀ pstar βP ηP ηH βH c B εTri ε χ:ℝ)
    (hpstar:0<pstar)
    (hselector:OrdinaryTriangleFixedDomainSelector k d M hd (max (1/2) (cycleThreshold 3)) α pstar
      (ρ₀/16) βP ηP ηH βH c B εTri ε χ (2*(3*d)) hpstar)
    (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (D vsize:ℕ) (β:ℝ) (Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (pR pH:ℝ) (hpR:pstar≤pR) (hpR1:pR≤1) (hpH:pstar≤pH) (hpH1:pH≤1) (L:ℕ)
    (hinputs:OrdinaryVortexGeneralParentInputBundle Q π hπ 2 d L M α ρ₀ εTri pR pH):
    let W:=markedVortexVertexType Q;let Z:=markedVortexHubType Q;
    let f:=fun i=>(markedVortexVertexEmbedding Q i).toEmbedding;
    let g:=fun i=>markedVortexHubEmbedding Q i;
    let ρ:=markedVortexPermutation Q π hπ;
    let F:=permutationConflictGraph π (3*d);
    Nonempty (OrdinaryTriangleFullDomainSelection k d hd
      (max (1/2) (cycleThreshold 3)) α pstar (ρ₀/16) βP ηP ηH βH c B εTri χ (2*(3*d)) hpstar
      V U Γ Color W Z P F f g ρ L) :=by
  intro W Z f g ρ F
  dsimp only [OrdinaryVortexGeneralParentInputBundle] at hinputs
  obtain ⟨hsize,hstep,hhubs,hmin,hconfdeg,hconf,hshort,hmean,hreglocal,hmeanEq⟩:=hinputs
  exact ordinary_triangle_full_domain_selection k d M hd
    (max (1/2) (cycleThreshold 3)) α pstar (ρ₀/16) βP ηP ηH βH c B εTri ε χ (2*(3*d)) hpstar
    hselector V U Γ Color W Z P F f g ρ L hsize hstep hmin
end Oberwolfach
