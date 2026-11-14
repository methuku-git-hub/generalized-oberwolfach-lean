module

public import Oberwolfach.OrdinaryExpandedFixedVortexRimCuts
public import Oberwolfach.FiniteProductRegrouping

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_expanded_fixed_vortex_rim_cuts_from_prior
    (α αcut pstar β ε ρ₀ χ:ℝ)
    (hα:0<α) (hαcut:0<αcut) (hαcut1:αcut≤1/2) (hαcutα:αcut≤α/2)
    (hpstar:0<pstar) (hβ:0≤β) (hβα:β≤α/8) (hβ1:β≤1/4)
    (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hχ:0<χ):
    ∃v₀:ℕ,1≤v₀ ∧ ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀(P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (1/2+α)*Fintype.card V≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize),
    ∀(p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1),pstar≤2*p→
    ∀d:ℕ,∀hd:2≤d,
    ∀(q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
      (s:U→Color→ℝ) (hs:∀w j,0≤s w j)
      (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g)),
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
      (E:(Σσ,R σ)→Prop) (εE:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    let κ:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.fairCoin);
    1-εE≤(μ.sigma ν).probability E→
    1-(εE+χ)≤((μ.sigma ν).prod κ).probability (fun z=>E z.1∧∀i,i<Q.length→
      OrdinaryInducedRimCutEvent (Q.extendedVertices (i+1))
        (sampledOrientation (rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) z.2) αcut pstar):=by
  obtain ⟨v₀,hv₀,hmain⟩:=ordinary_expanded_fixed_vortex_rim_cuts α αcut pstar β ε ρ₀ χ
    hα hαcut hαcut1 hαcutα hpstar hβ hβα hβ1 hε hε1 hρ₀ hχ
  refine ⟨v₀,hv₀,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D vsize hreg hn hdegree hρlo hρhi hv Q
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum hpstarR d hd q hq hQ s hs hS R _ ν E εE μ κ hE
  have hprior:1-εE≤((μ.sigma ν).prod κ).probability (fun z=>E z.1):=by
    rw [finiteLaw_prod_first_probability]
    exact hE
  exact hmain V U Γ Color P D vsize hreg hn hdegree hρlo hρhi hv Q
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum hpstarR d hd q hq hQ s hs hS ν (fun z=>E z.1) εE hprior
end Oberwolfach
