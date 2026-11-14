module

public import Oberwolfach.OrdinaryReferenceCutsDomainSelector
public import Oberwolfach.OrdinaryVortexParentInputsFromOriginal

@[expose] public section
/-! Apply the preselected all-domain triangle event to the full parents of
the actual regular-host vortex, choosing weights before the raw sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_full_parent_reference_cuts
    (k d M:ℕ) (hd:2≤d) (α ρ₀ pstar δ h εTri ε χ:ℝ)
    (hpstar:0<pstar)
    (hselector:OrdinaryReferenceCutsDomainSelector d M hd α pstar (ρ₀/16) δ h ε χ (2*(3*d)))
    (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (D vsize:ℕ) (β:ℝ) (Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hα:0<α) (hdegree:(max (1/2) (cycleThreshold 3)+2*α)*Fintype.card V≤D)
    (hρ₀:0<ρ₀) (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hβ:0≤β) (hβα:β≤α/4) (hβ1:β≤1/4) (hβε:β≤εTri)
    (hε:0<ε) (hε1:ε≤1) (hερ:ε≤ρ₀/16) (hvsize:0<vsize)
    (hnoshort:∀x t,0<t→t<2*d+1→(π^t) x≠x)
    (pR pH:ℝ) (hpR:pstar≤pR) (hpR1:pR≤1) (hpH:pstar≤pH) (hpH1:pH≤1)
    (hpEq:pR=initialIndexDensity U D*pH)
    (L:ℕ) (hL:L<Q.length) (hM:(M:ℝ)≤ε*vsize/2):
    let W:=markedVortexVertexType Q;let Z:=markedVortexHubType Q
    let f:=fun i=>(markedVortexVertexEmbedding Q i).toEmbedding
    let g:=fun i=>markedVortexHubEmbedding Q i
    let ρ:=markedVortexPermutation Q π hπ
    let F:=permutationConflictGraph π (3*d);
    ∀(q:U→Γ→ℝ) (hq:∀u z,0≤q u z) (hQ:∀u,∑z,q u z≤1/8)
      (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
      (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑z,q u z)) (j:Color) (hj:∀u,s u j=pH),
    let μ:=FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>pR) (fun _=>(hpstar.trans_le hpR).le) (fun _=>hpR1) d hd q hq hQ s hs hS)
    let ν:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.fairCoin);
    1-χ≤(μ.prod ν).probability (fun z=>∀i≤L,
      OrdinaryTriangleReferenceNormalizedCuts (P.comap (f i)) (F.comap (f i)) (ρ i) d j δ h
        (ordinaryRawRestrictPair (f i) (g i) z.1) (fun e=>z.2 (Sym2.map (f i) e))) :=by
  intro W Z f g ρ F
  have hfields:=ordinary_vortex_parent_inputs_from_original P D vsize d β ε α ρ₀ pstar εTri pR pH
    Q π hπ hreg hn hα hdegree hρ₀ hρlo hρhi hβ hβα hβ1 hβε hε hε1 hερ hvsize hnoshort
    hpR hpR1 hpH hpH1 hpEq L M hL hM
  obtain ⟨hdeep,hsize,hstep,hhubs,hmin,hconfdeg,hconf,hshort,hmean,hreglocal,hmeanEq⟩:=hfields
  have hsize':∀i≤L,M≤(Finset.univ:Finset (W i)).card:=by simpa only [Finset.card_univ] using hsize
  have hstep':∀i<L,(((Finset.univ:Finset (W (i+1))).card):ℝ)≤ε*(Finset.univ:Finset (W i)).card:=by
    simpa only [Finset.card_univ] using hstep
  have hhalf:∀i≤L,∀v,(1/2+α)*Fintype.card (W i)≤((P.comap (f i)).degree v:ℝ):=by
    intro i hi v
    have hc:(1/2+α:ℝ)≤max (1/2) (cycleThreshold 3)+α:=by have hh:=le_max_left (1/2:ℝ) (cycleThreshold 3);linarith
    exact (mul_le_mul_of_nonneg_right hc (by positivity)).trans (hmin i hi v)
  intro q hq hQ s hs hS j hj μ ν
  exact hselector V U Γ Color W Z P F f g ρ (fun _=>Finset.univ) L hsize' hstep' hhubs hhalf hconfdeg hshort
    pR pH (hpstar.trans_le hpR).le hpR1 hpR hpH q hq hQ s hs hS j hj
end Oberwolfach
