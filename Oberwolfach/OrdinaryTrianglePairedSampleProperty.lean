module

public import Oberwolfach.OrdinaryExpandedVortexTrianglePairedSupportedSample

@[expose] public section
/-! A named property for attaching the selected full-parent tests to any
prior on the same expanded sample and fair reference coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryTrianglePairedSampleProperty
    (k d:ℕ) (hd:2≤d)
    (α ρ₀ pstar βP ηP ηH βH c B ε χhost δ h χcut:ℝ)
    (hpstar:0<pstar)
    : Prop :=
    ∃εTri:ℝ,0<εTri ∧ ∃Mhost Mcut:ℕ,1≤Mhost ∧ 1≤Mcut ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (D vsize:ℕ) (β:ℝ) (Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hα:0<α) (θhost:ℝ) (hθ:1/2≤θhost) (hthreshold:cycleThreshold 3≤θhost)
    (hdegree:(θhost+α)*Fintype.card V ≤ D)
    (hρ₀:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D ≤ 1)
    (hβ:0 ≤ β) (hβα:β ≤ α/8) (hβ1:β ≤ 1/4) (hβε:β ≤ εTri)
    (hε:0<ε) (hε1:ε ≤ 1) (hερ:ε ≤ ρ₀/16) (hvsize:0<vsize)
    (hnoshort:∀x t,0<t → t<2*d+1 → (π^t) x≠x)
    (p k₂ k₁ u v:ℝ) (hp:0 ≤ p) (hk₂:0 ≤ k₂) (hk₁:0 ≤ k₁) (hu:0 ≤ u) (hv:0 ≤ v)
    (hsum:2*p+2*k₂+2*k₁+2*u+v ≤ 1) (pH:ℝ)
    (hpR:pstar ≤ 2*p) (hpH:pstar ≤ pH) (hpH1:pH ≤ 1) (hpEq:2*p=initialIndexDensity U D*pH)
    (L:ℕ) (hL:L<Q.length) (hMhost:(Mhost:ℝ) ≤ ε*vsize/2) (hMcut:(Mcut:ℝ) ≤ ε*vsize/2),
    let W:=markedVortexVertexType Q;let Z:=markedVortexHubType Q;
    let f:=fun i=>(markedVortexVertexEmbedding Q i).toEmbedding;
    let g:=fun i=>markedVortexHubEmbedding Q i;
    let ρi:=markedVortexPermutation Q π hπ;
    let F:=permutationConflictGraph π (3*d);
    ∃selection:OrdinaryTriangleFullDomainSelection k d hd
      (max (1/2) (cycleThreshold 3)) (α/2) pstar (ρ₀/16) βP ηP ηH βH c B εTri χhost (2*(3*d)) hpstar
      V U Γ Color W Z P F f g ρi L,
    ∀(q:U → Γ → ℝ) (hq:∀u z,0 ≤ q u z) (hQ:∀u,∑z,q u z ≤ 1/8)
      (s:U → Color → ℝ) (hs:∀u j,0 ≤ s u j)
      (hS:∀u,∑j,s u j ≤ intervalUncoveredProbability d (∑z,q u z)) (j:Color) (hj:∀u,s u j=pH),
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) → Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
      (E:(Σσ,R σ)×(Sym2 V → Bool) → Prop) (a:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k₂ k₁ u v hp hk₂ hk₁ hu hv hsum d hd q hq hQ s hs hS);
    let κ:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.fairCoin);
    let Host:RawWheelOutcome V U Γ Color → Prop:=fun raw=>∀i ≤ L,
      ordinaryCombinedTriangleEvent d k (P.comap (f i)) (F.comap (f i)) (ρi i)
        (max (1/2) (cycleThreshold 3)) (α/2) pstar βP ηP ηH βH c B (2*p) pH (selection.weight i)
        j (ordinaryRawRestrictPair (f i) (g i) raw);
    let Cuts:RawWheelOutcome V U Γ Color×(Sym2 V → Bool) → Prop:=fun z=>∀i ≤ L,
      OrdinaryTriangleReferenceNormalizedCuts (P.comap (f i)) (F.comap (f i)) (ρi i) d j δ h
        (ordinaryRawRestrictPair (f i) (g i) z.1) (fun e=>z.2 (Sym2.map (f i) e));
    1-a ≤ ((μ.sigma ν).prod κ).probability E →
    let All:=fun z=>E z ∧ Host (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)) ∧
      Cuts ((fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)),z.2);
    1-a-χhost-χcut ≤ ((μ.sigma ν).prod κ).probability All ∧
      (0<1-a-χhost-χcut → ∃z,0<((μ.sigma ν).prod κ).mass z ∧ All z)

theorem ordinary_triangle_paired_sample_property_of_choice
    (k d:ℕ) (hd:2≤d)
    (α ρ₀ pstar βP ηP ηH βH c B ε χhost δ h χcut:ℝ)
    (hpstar:0<pstar)
    (hchoice:∃εTri:ℝ,0<εTri ∧ ∃Mhost Mcut:ℕ,1≤Mhost ∧ 1≤Mcut ∧
      OrdinaryTriangleFixedDomainSelector k d Mhost hd (max (1/2) (cycleThreshold 3)) (α/2) pstar
        (ρ₀/16) βP ηP ηH βH c B εTri ε χhost (2*(3*d)) hpstar ∧
      OrdinaryReferenceCutsDomainSelector d Mcut hd (α/2) pstar (ρ₀/16) δ h ε χcut (2*(3*d))) :
    OrdinaryTrianglePairedSampleProperty k d hd α ρ₀ pstar βP ηP ηH βH c B ε χhost δ h χcut hpstar :=by
  exact ordinary_expanded_vortex_triangle_paired_supported_sample k d hd α ρ₀ pstar βP ηP ηH βH c B ε χhost δ h χcut hpstar hchoice
end Oberwolfach
