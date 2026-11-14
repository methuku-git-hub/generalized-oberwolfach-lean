module

public import Oberwolfach.OrdinaryExpandedVortexParentSelectionCommon
public import Oberwolfach.FiniteLawPositiveLowerBoundWitness

@[expose] public section
/-! Choose the actual vortex's parent weights before sampling, then attach
all parent and reference-direction tests to any prior on the same expanded
sample and the same fair reference coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_expanded_vortex_parent_common_witness
    (mWheel k d Mhost Mcut:ℕ) (hm:3 ≤ mWheel) (hd:2 ≤ d)
    (α ρ₀ pstar βP ηP row ηH βH c B εTri ε χhost δ h χcut:ℝ)
    (hpstar:0<pstar)
    (hcuts:OrdinaryReferenceCutsDomainSelector d Mcut hd α pstar (ρ₀/16) δ h ε χcut (2*(3*d)))
    (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (D vsize:ℕ) (β:ℝ) (Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hα:0<α) (hdegree:(max (1/2) (cycleThreshold (mWheel+1))+2*α)*Fintype.card V ≤ D)
    (hρ₀:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D ≤ 1)
    (hβ:0 ≤ β) (hβα:β ≤ α/4) (hβ1:β ≤ 1/4) (hβε:β ≤ εTri)
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
    ∀selection:OrdinaryGeneralFullDomainSelection mWheel k d hm hd
      (max (1/2) (cycleThreshold (mWheel+1))) α pstar (ρ₀/16) βP ηP row ηH βH c B εTri χhost (2*(3*d)) hpstar
      V U Γ Color W Z P F f g ρi L,
    ∀(q:U → Γ → ℝ) (hq:∀u z,0 ≤ q u z) (hQ:∀u,∑z,q u z ≤ 1/8)
      (s:U → Color → ℝ) (hs:∀u j,0 ≤ s u j)
      (hS:∀u,∑j,s u j ≤ intervalUncoveredProbability d (∑z,q u z)) (j:Color) (hj:∀u,s u j=pH),
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) → Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
      (Good:(Σσ,R σ)×(Sym2 V → Bool) → Prop) (b:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k₂ k₁ u v hp hk₂ hk₁ hu hv hsum d hd q hq hQ s hs hS);
    let κ:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.fairCoin);
    let Host:RawWheelOutcome V U Γ Color → Prop:=fun raw=>∀i ≤ L,
      ordinaryCombinedHostEvent mWheel d k hm (P.comap (f i)) (F.comap (f i)) (ρi i)
        (max (1/2) (cycleThreshold (mWheel+1))) α pstar βP ηP row ηH βH c B (2*p) pH (selection.weight i)
        (fun z=>s (g i z)) j (ordinaryRawRestrictPair (f i) (g i) raw);
    let Cuts:RawWheelOutcome V U Γ Color×(Sym2 V → Bool) → Prop:=fun z=>∀i ≤ L,
      OrdinaryTriangleReferenceNormalizedCuts (P.comap (f i)) (F.comap (f i)) (ρi i) d j δ h
        (ordinaryRawRestrictPair (f i) (g i) z.1) (fun e=>z.2 (Sym2.map (f i) e));
    b≤((μ.sigma ν).prod κ).probability Good →
    let All:=fun z=>Good z ∧ Host (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)) ∧
      Cuts ((fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)),z.2);
    b-χhost-χcut≤((μ.sigma ν).prod κ).probability All ∧
      (0<b-χhost-χcut → ∃z,0<((μ.sigma ν).prod κ).mass z ∧ All z) :=by
  intro W Z f g ρi F selection q hq hQ s hs hS j hj R _ ν Good b μ κ Host Cuts hGood All
  have hprior:1-(1-b)≤((μ.sigma ν).prod κ).probability Good:=by linarith only [hGood]
  have hh:=ordinary_expanded_vortex_parent_selection_common mWheel k d Mhost Mcut hm hd
    α ρ₀ pstar βP ηP row ηH βH c B εTri ε χhost δ h χcut hpstar hcuts
    V U Γ Color P D vsize β Q π hπ hreg hn hα hdegree hρ₀ hρlo hρhi hβ hβα hβ1 hβε hε hε1 hερ hvsize hnoshort
    p k₂ k₁ u v hp hk₂ hk₁ hu hv hsum pH hpR hpH hpH1 hpEq L hL hMhost hMcut
    selection q hq hQ s hs hS j hj ν Good (1-b) hprior
  have hprob:b-χhost-χcut≤((μ.sigma ν).prod κ).probability All:=by
    change 1-(1-b)-χhost-χcut≤((μ.sigma ν).prod κ).probability All at hh
    linarith only [hh]
  exact ⟨hprob,fun hb=>finiteLaw_positive_lower_bound_witness ((μ.sigma ν).prod κ) All _ hb hprob⟩
end Oberwolfach
