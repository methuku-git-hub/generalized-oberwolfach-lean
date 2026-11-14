module

public import Oberwolfach.OrdinaryVortexFullParentSelectionProbability
public import Oberwolfach.OrdinaryExpandedRawEventProductPrior

@[expose] public section
/-! Attach the selected full-parent tests to any prior on the same expanded
outcome and reference coins, with the weight family fixed in advance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_expanded_vortex_parent_selection_event
    (mWheel k d M:ℕ) (hm:3 ≤ mWheel) (hd:2 ≤ d) (α ρ₀ pstar βP ηP row ηH βH c B εTri ε χ:ℝ)
    (hpstar:0<pstar)
    (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (D mv:ℕ) (β:ℝ) (Q:Vortex U P D β ε mv) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (p k₁ p₂ k₂ u:ℝ) (hp:0 ≤ p) (hk₁:0 ≤ k₁) (hp₂:0 ≤ p₂) (hk₂:0 ≤ k₂) (hu:0 ≤ u)
    (hsum:2*p+2*k₁+2*p₂+2*k₂+u ≤ 1) (pH:ℝ)
    (hpR:pstar ≤ 2*p) (hpH:pstar ≤ pH) (hpH1:pH ≤ 1) (L:ℕ)
    (hinputs:OrdinaryVortexGeneralParentInputBundle Q π hπ mWheel d L M α ρ₀ εTri (2*p) pH):
    let W:=markedVortexVertexType Q;let Z:=markedVortexHubType Q;
    let f:=fun i=>(markedVortexVertexEmbedding Q i).toEmbedding;
    let g:=fun i=>markedVortexHubEmbedding Q i;
    let ρi:=markedVortexPermutation Q π hπ;
    let F:=permutationConflictGraph π (3*d);
    ∀selection:OrdinaryGeneralFullDomainSelection mWheel k d hm hd
      (max (1/2) (cycleThreshold (mWheel+1))) α pstar (ρ₀/16) βP ηP row ηH βH c B εTri χ (2*(3*d)) hpstar
      V U Γ Color W Z P F f g ρi L,
    ∀(q:U → Γ → ℝ) (hq:∀w z,0 ≤ q w z) (hQ:∀w,∑z,q w z ≤ 1/8)
      (s:U → Color → ℝ) (hs:∀w j,0 ≤ s w j)
      (hS:∀w,∑j,s w j ≤ intervalUncoveredProbability d (∑z,q w z)) (j:Color) (hj:∀w,s w j=pH),
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) → Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (κ:FiniteLaw (Sym2 V → Bool))
      (E:(Σσ,R σ)×(Sym2 V → Bool) → Prop) (a:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k₁ p₂ k₂ u hp hk₁ hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    let Host:RawWheelOutcome V U Γ Color → Prop:=fun raw=>∀i ≤ L,
      ordinaryCombinedHostEvent mWheel d k hm (P.comap (f i)) (F.comap (f i)) (ρi i)
        (max (1/2) (cycleThreshold (mWheel+1))) α pstar βP ηP row ηH βH c B (2*p) pH (selection.weight i)
        (fun z=>s (g i z)) j (ordinaryRawRestrictPair (f i) (g i) raw);
    1-a ≤ ((μ.sigma ν).prod κ).probability E → 
    1-a-χ ≤ ((μ.sigma ν).prod κ).probability (fun z=>E z ∧
      Host (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) :=by
  intro W Z f g ρi F selection q hq hQ s hs hS j hj R _ ν κ E a μ Host hE
  have hpR1:2*p ≤ 1:=by linarith
  have hraw:=ordinary_vortex_full_parent_selection_probability mWheel k d M hm hd α ρ₀ pstar βP ηP row ηH βH c B εTri ε χ
    hpstar V U Γ Color P D mv β Q π hπ (2*p) pH hpR hpR1 hpH hpH1 L hinputs selection q hq hQ s hs hS j hj
  apply ordinary_expanded_add_raw_event_with_product_prior p k₁ p₂ k₂ u hp hk₁ hp₂ hk₂ hu hsum d hd q hq hQ s hs hS
    ν κ E Host a χ hE
  convert hraw using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
