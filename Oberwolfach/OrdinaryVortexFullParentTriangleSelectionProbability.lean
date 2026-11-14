module

public import Oberwolfach.OrdinaryVortexFullParentTriangleSelectionFromBundle

@[expose] public section
/-! Specialize the selected family's probability callback to the actual
vortex means and conflict graph, separately from choosing the weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_full_parent_triangle_selection_probability
    (k d M:ℕ) (hd:2≤d) (α ρ₀ pstar βP ηP ηH βH c B εTri ε χ:ℝ)
    (hpstar:0<pstar)
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
    ∀selection:OrdinaryTriangleFullDomainSelection k d hd
      (max (1/2) (cycleThreshold 3)) α pstar (ρ₀/16) βP ηP ηH βH c B εTri χ (2*(3*d)) hpstar
      V U Γ Color W Z P F f g ρ L,
    ∀(q:U→Γ→ℝ) (hq:∀u z,0≤q u z) (hQ:∀u,∑z,q u z≤1/8)
      (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
      (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑z,q u z)) (j:Color) (hj:∀u,s u j=pH),
    let μ:=FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>pR) (fun _=>(hpstar.trans_le hpR).le) (fun _=>hpR1) d hd q hq hQ s hs hS);
    1-χ≤μ.probability (fun raw=>∀i≤L,ordinaryCombinedTriangleEvent d k (P.comap (f i)) (F.comap (f i)) (ρ i)
      (max (1/2) (cycleThreshold 3)) α pstar βP ηP ηH βH c B pR pH (selection.weight i) j
      (ordinaryRawRestrictPair (f i) (g i) raw)) :=by
  intro W Z f g ρ F selection q hq hQ s hs hS j hj μ
  dsimp only [OrdinaryVortexGeneralParentInputBundle] at hinputs
  obtain ⟨hsize,hstep,hhubs,hmin,hconfdeg,hconf,hshort,hmean,hreglocal,hmeanEq⟩:=hinputs
  have hh:=selection.sample pR pH (fun i=>2*(Fintype.card (Z i):ℝ)/initialIndexDensity U D) hhubs hconfdeg hconf hshort
    hpR hpR1 hpH hpH1 hmean hreglocal hmeanEq q hq hQ s hs hS j hj
  convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
