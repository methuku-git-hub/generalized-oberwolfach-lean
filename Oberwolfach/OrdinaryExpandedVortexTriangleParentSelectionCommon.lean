module

public import Oberwolfach.OrdinaryExpandedVortexTriangleParentSelectionEvent
public import Oberwolfach.OrdinaryExpandedVortexParentReferenceCuts

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

theorem ordinary_expanded_vortex_triangle_parent_selection_common
    (k d Mhost Mcut:ℕ) (hd:2 ≤ d)
    (α ρ₀ pstar βP ηP ηH βH c B εTri ε χhost δ h χcut:ℝ)
    (hpstar:0<pstar)
    (hcuts:OrdinaryReferenceCutsDomainSelector d Mcut hd α pstar (ρ₀/16) δ h ε χcut (2*(3*d)))
    (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (D vsize:ℕ) (β:ℝ) (Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hα:0<α) (hdegree:(max (1/2) (cycleThreshold 3)+2*α)*Fintype.card V ≤ D)
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
    ∀selection:OrdinaryTriangleFullDomainSelection k d hd
      (max (1/2) (cycleThreshold 3)) α pstar (ρ₀/16) βP ηP ηH βH c B εTri χhost (2*(3*d)) hpstar
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
        (max (1/2) (cycleThreshold 3)) α pstar βP ηP ηH βH c B (2*p) pH (selection.weight i)
        j (ordinaryRawRestrictPair (f i) (g i) raw);
    let Cuts:RawWheelOutcome V U Γ Color×(Sym2 V → Bool) → Prop:=fun z=>∀i ≤ L,
      OrdinaryTriangleReferenceNormalizedCuts (P.comap (f i)) (F.comap (f i)) (ρi i) d j δ h
        (ordinaryRawRestrictPair (f i) (g i) z.1) (fun e=>z.2 (Sym2.map (f i) e));
    1-a ≤ ((μ.sigma ν).prod κ).probability E → 
    1-a-χhost-χcut ≤ ((μ.sigma ν).prod κ).probability (fun z=>E z ∧
      Host (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)) ∧
      Cuts ((fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)),z.2)) :=by
  intro W Z f g ρi F selection q hq hQ s hs hS j hj R _ ν E a μ κ Host Cuts hE
  have hpR1:2*p≤1:=by linarith
  have hinputs:=ordinary_vortex_general_parent_input_bundle_from_original 2 (by omega) P D vsize d β ε α ρ₀
    pstar εTri (2*p) pH Q π hπ hreg hn hα hdegree hρ₀ hρlo hρhi hβ hβα hβ1 hβε hε hε1 hερ hvsize
    hnoshort hpR hpR1 hpH hpH1 hpEq L Mhost hL hMhost
  have hfirst:=ordinary_expanded_vortex_triangle_parent_selection_event k d Mhost hd α ρ₀ pstar βP ηP ηH βH c B εTri ε χhost
    hpstar V U Γ Color P D vsize β Q π hπ p k₂ k₁ u v hp hk₂ hk₁ hu hv hsum pH hpR hpH hpH1 L hinputs
    selection q hq hQ s hs hS j hj ν κ E a hE
  let Ehost:=fun z:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)×(Sym2 V→Bool)=>
    E z ∧ Host (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))
  have hfirst':1-(a+χhost)≤((μ.sigma ν).prod κ).probability Ehost:=by
    change 1-a-χhost≤((μ.sigma ν).prod κ).probability Ehost at hfirst
    linarith only [hfirst]
  have hsecond:=ordinary_expanded_vortex_parent_reference_cuts 2 k d Mcut (by omega) hd
    α ρ₀ pstar δ h εTri ε χcut hpstar hcuts V U Γ Color P D vsize β Q π hπ
    hreg hn hα hdegree hρ₀ hρlo hρhi hβ hβα hβ1 hβε hε hε1 hερ hvsize hnoshort
    p k₂ k₁ u v hp hk₂ hk₁ hu hv hsum pH hpR hpH hpH1 hpEq L hL hMcut
    q hq hQ s hs hS j hj ν Ehost (a+χhost) hfirst'
  simpa only [Ehost,and_assoc,sub_add_eq_sub_sub] using hsecond
end Oberwolfach
