module

public import Oberwolfach.OrdinaryTriangleCommonSampleBundle
public import Oberwolfach.OrdinaryExpandedVortexTriangleParentSupportedSample
public import Oberwolfach.FiniteLawPositiveEventWitness
public import Oberwolfach.OrdinaryExpandedVortexTriangleParentFromOriginalMargin
public import Oberwolfach.OrdinaryTriangleParentHostBounds
public import Oberwolfach.OrdinaryExpandedVortexTriangleParentCommonSelected
public import Oberwolfach.OrdinaryVortexFullParentTriangleSelectionFromOriginal
public import Oberwolfach.OrdinaryExpandedVortexTriangleParentSelectionCommon
public import Oberwolfach.OrdinaryExpandedVortexTriangleParentSelectionEvent
public import Oberwolfach.OrdinaryExpandedVortexParentReferenceCuts

@[expose] public section
/-! Choose the actual vortex's parent weights before sampling, then attach
all parent and reference-direction tests to any prior on the same expanded
sample and the same fair reference coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := 100000) triangleBundleParentFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_triangle_common_bundle_parent_supported
    (k d Mhost Mcut:ℕ) (hd:2 ≤ d)
    (α ρ₀ pstar βP ηP ηH βH c B εTri ε χhost δ h χcut:ℝ)
    (hpstar:0<pstar)
    (hselector:OrdinaryTriangleFixedDomainSelector k d Mhost hd (max (1/2) (cycleThreshold 3)) (α/2) pstar
      (ρ₀/16) βP ηP ηH βH c B εTri ε χhost (2*(3*d)) hpstar)
    (hcuts:OrdinaryReferenceCutsDomainSelector d Mcut hd (α/2) pstar (ρ₀/16) δ h ε χcut (2*(3*d)))
    (n:ℕ) (U:Type) [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (D vsize:ℕ) (β:ℝ) (Q:Vortex U P D β ε vsize) (π:Equiv.Perm (Fin n))
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card (Fin n))
    (hα:0<α) (θhost:ℝ) (hθ:1/2≤θhost) (hthreshold:cycleThreshold 3≤θhost)
    (hdegree:(θhost+α)*Fintype.card (Fin n) ≤ D)
    (hρ₀:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D ≤ 1)
    (hβ:0 ≤ β) (hβα:β ≤ α/8) (hβ1:β ≤ 1/4) (hβε:β ≤ εTri)
    (hε:0<ε) (hε1:ε ≤ 1) (hερ:ε ≤ ρ₀/16) (hvsize:0<vsize)
    (hnoshort:∀x t,0<t → t<2*d+1 → (π^t) x≠x)
    (p k₂ k₁ u v:ℝ) (hp:0 ≤ p) (hk₂:0 ≤ k₂) (hk₁:0 ≤ k₁) (hu:0 ≤ u) (hv:0 ≤ v)
    (hsum:2*p+2*k₂+2*k₁+2*u+v ≤ 1) (pH:ℝ)
    (hpR:pstar ≤ 2*p) (hpH:pstar ≤ pH) (hpH1:pH ≤ 1) (hpEq:2*p=initialIndexDensity U D*pH)
    (L:ℕ) (hL:L<Q.length) (hMhost:(Mhost:ℝ) ≤ ε*vsize/2) (hMcut:(Mcut:ℝ) ≤ ε*vsize/2):
    let W:=markedVortexVertexType Q;let Z:=markedVortexHubType Q;
    let f:=fun i=>(markedVortexVertexEmbedding Q i).toEmbedding;
    let g:=fun i=>markedVortexHubEmbedding Q i;
    let ρi:=markedVortexPermutation Q π hπ;
    let F:=permutationConflictGraph π (3*d);
    ∃selection:OrdinaryTriangleFullDomainSelection k d hd
      (max (1/2) (cycleThreshold 3)) (α/2) pstar (ρ₀/16) βP ηP ηH βH c B εTri χhost (2*(3*d)) hpstar
      (Fin n) U Bool Bool W Z P F f g ρi L,
    ∀(q:U → Bool → ℝ) (hq:∀u z,0 ≤ q u z) (hQ:∀u,∑z,q u z ≤ 1/8)
      (s:U → Bool → ℝ) (hs:∀u j,0 ≤ s u j)
      (hS:∀u,∑j,s u j ≤ intervalUncoveredProbability d (∑z,q u z)) (j:Bool) (hj:∀u,s u j=pH),
    ∀(εR εH θsample κCover αcut pmin δcap βe βh b Bweight ηHub tpot:ℝ)
      (weight:∀i,markedVortexVertexType Q i→Sym2 (markedVortexVertexType Q i⊕markedVortexHubType Q i)→ℝ)
      (m aK bK:ℕ) (ξCorr:ℝ),
    ∀{R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e) → Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
      (E:(Σσ,R σ)→Prop) (a:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p k₂ k₁ u v hp hk₂ hk₁ hu hv hsum d hd q hq hQ s hs hS);
    let κ:=FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.fairCoin);
    let Host:RawWheelOutcome (Fin n) U Bool Bool → Prop:=fun raw=>∀i ≤ L,
      ordinaryCombinedTriangleEvent d k (P.comap (f i)) (F.comap (f i)) (ρi i)
        (max (1/2) (cycleThreshold 3)) (α/2) pstar βP ηP ηH βH c B (2*p) pH (selection.weight i)
        j (ordinaryRawRestrictPair (f i) (g i) raw);
    let Cuts:RawWheelOutcome (Fin n) U Bool Bool×(Sym2 (Fin n) → Bool) → Prop:=fun z=>∀i ≤ L,
      OrdinaryTriangleReferenceNormalizedCuts (P.comap (f i)) (F.comap (f i)) (ρi i) d j δ h
        (ordinaryRawRestrictPair (f i) (g i) z.1) (fun e=>z.2 (Sym2.map (f i) e));
    let Good:=OrdinaryTriangleCommonSampleBundle P D vsize d β ε Q π hπ εR εH (2*p) pH θsample
      κCover αcut pmin δcap βe βh b Bweight ηHub tpot s j weight m aK bK ξCorr E;
    1-a ≤ ((μ.sigma ν).prod κ).probability Good →
    let All:=fun z=>Good z ∧ Host (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)) ∧
      Cuts ((fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)),z.2);
    1-a-χhost-χcut ≤ ((μ.sigma ν).prod κ).probability All ∧
      (0<1-a-χhost-χcut → ∃z,0<((μ.sigma ν).prod κ).mass z ∧ All z) :=by
  intro W Z f g ρi F
  obtain ⟨selection,hmain⟩:=ordinary_expanded_vortex_triangle_parent_supported_sample k d Mhost Mcut hd
    α ρ₀ pstar βP ηP ηH βH c B εTri ε χhost δ h χcut hpstar hselector hcuts
    (Fin n) U Bool Bool P D vsize β Q π hπ hreg hn hα θhost hθ hthreshold hdegree hρ₀ hρlo hρhi hβ hβα hβ1 hβε
    hε hε1 hερ hvsize hnoshort p k₂ k₁ u v hp hk₂ hk₁ hu hv hsum pH hpR hpH hpH1 hpEq L hL hMhost hMcut
  refine ⟨selection,?_⟩
  intro q hq hQ s hs hS j hj εR εH θsample κCover αcut pmin δcap βe βh b Bweight ηHub tpot weight m aK bK ξCorr
    R _ ν E a μ κ Host Cuts Good hE All
  exact hmain q hq hQ s hs hS j hj ν Good a hE
end Oberwolfach
