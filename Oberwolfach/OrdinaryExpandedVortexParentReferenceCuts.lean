module

public import Oberwolfach.OrdinaryVortexFullParentGeneralReferenceCuts
public import Oberwolfach.OrdinaryExpandedRawCoinEventProductPrior

@[expose] public section
/-! Attach every full-parent reference-cut test to any prior event on the
same expanded sample and the same fair direction coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_expanded_vortex_parent_reference_cuts
    (mWheel k d M:ℕ) (hm:2 ≤ mWheel) (hd:2 ≤ d) (α ρ₀ pstar δ h εTri ε χ:ℝ)
    (hpstar:0<pstar)
    (hselector:OrdinaryReferenceCutsDomainSelector d M hd α pstar (ρ₀/16) δ h ε χ (2*(3*d)))
    (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (D mv:ℕ) (β:ℝ) (Q:Vortex U P D β ε mv) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V) (hα:0<α)
    (hdegree:(max (1/2) (cycleThreshold (mWheel+1))+2*α)*Fintype.card V ≤ D)
    (hρ₀:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D ≤ 1)
    (hβ:0 ≤ β) (hβα:β ≤ α/4) (hβ1:β ≤ 1/4) (hβε:β ≤ εTri)
    (hε:0<ε) (hε1:ε ≤ 1) (hερ:ε ≤ ρ₀/16) (hmv:0<mv)
    (hnoshort:∀x t,0<t → t<2*d+1 → (π^t) x≠x)
    (p k₁ p₂ k₂ u:ℝ) (hp:0 ≤ p) (hk₁:0 ≤ k₁) (hp₂:0 ≤ p₂) (hk₂:0 ≤ k₂) (hu:0 ≤ u)
    (hsum:2*p+2*k₁+2*p₂+2*k₂+u ≤ 1) (pH:ℝ)
    (hpR:pstar ≤ 2*p) (hpH:pstar ≤ pH) (hpH1:pH ≤ 1) (hpEq:2*p=initialIndexDensity U D*pH)
    (L:ℕ) (hL:L<Q.length) (hM:(M:ℝ) ≤ ε*mv/2):
    let f:=fun i=>(markedVortexVertexEmbedding Q i).toEmbedding;
    let g:=fun i=>markedVortexHubEmbedding Q i;
    let ρi:=markedVortexPermutation Q π hπ;
    let F:=permutationConflictGraph π (3*d);
    ∀(q:U → Γ → ℝ) (hq:∀w z,0 ≤ q w z) (hQ:∀w,∑z,q w z ≤ 1/8)
      (s:U → Color → ℝ) (hs:∀w j,0 ≤ s w j)
      (hS:∀w,∑j,s w j ≤ intervalUncoveredProbability d (∑z,q w z)) (j:Color) (hj:∀w,s w j=pH),
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) → Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
      (E:(Σσ,R σ)×(Sym2 V → Bool) → Prop) (a:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k₁ p₂ k₂ u hp hk₁ hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    let κ:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.fairCoin);
    let Cuts:RawWheelOutcome V U Γ Color×(Sym2 V → Bool) → Prop:=fun z=>∀i ≤ L,
      OrdinaryTriangleReferenceNormalizedCuts (P.comap (f i)) (F.comap (f i)) (ρi i) d j δ h
        (ordinaryRawRestrictPair (f i) (g i) z.1) (fun e=>z.2 (Sym2.map (f i) e));
    1-a ≤ ((μ.sigma ν).prod κ).probability E → 
    1-a-χ ≤ ((μ.sigma ν).prod κ).probability (fun z=>E z ∧
      Cuts ((fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)),z.2)) :=by
  intro f g ρi F q hq hQ s hs hS j hj R _ ν E a μ κ Cuts hE
  have hpR1:2*p ≤ 1:=by linarith
  have hraw:=ordinary_vortex_full_parent_general_reference_cuts mWheel k d M hm hd α ρ₀ pstar δ h εTri ε χ hpstar hselector
    V U Γ Color P D mv β Q π hπ hreg hn hα hdegree hρ₀ hρlo hρhi hβ hβα hβ1 hβε hε hε1 hερ hmv hnoshort
    (2*p) pH hpR hpR1 hpH hpH1 hpEq L hL hM q hq hQ s hs hS j hj
  apply ordinary_expanded_add_raw_coin_event_with_product_prior p k₁ p₂ k₂ u hp hk₁ hp₂ hk₂ hu hsum d hd q hq hQ s hs hS
    ν κ E Cuts a χ hE
  convert hraw using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
