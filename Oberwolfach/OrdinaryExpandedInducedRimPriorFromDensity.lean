module

public import Oberwolfach.OrdinaryExpandedInducedRimPrior
public import Oberwolfach.OrdinaryInducedParentThreshold
public import Oberwolfach.OrdinaryInducedRimCutProbability
public import Oberwolfach.ExpandedOrdinarySelectedLaw
public import Oberwolfach.FiniteSigmaFirstMap

@[expose] public section
/-! Add the induced rim cut to any prior event of the full expanded sample
    and the same physical direction coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_expanded_induced_rim_cut_with_prior_from_density
    (α pstar:ℝ) (hα:0<α) (hα1:α≤1/2) (hpstar:0<pstar) (q₀:ℕ):
    ∃N:ℕ,∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀(P:SimpleGraph V) (I:Finset V),N≤I.card→
      ∀ density : ℝ, cycleThreshold 3 + α ≤ density →
      (∀ v, density * I.card ≤ ((I ∩ P.neighborFinset v).card : ℝ)) →
    ∀(p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1),pstar≤2*p→
    ∀d:ℕ,∀hd:2≤d,
    ∀(q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
      (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g)),
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
      [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ))
      (E:(Σσ,R σ)×(Sym2 V→Bool)→Prop) (a:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    let ν:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.fairCoin);
    1-a≤((μ.sigma ρ).prod ν).probability E→
    1-a-1/(I.card:ℝ)^q₀≤((μ.sigma ρ).prod ν).probability (fun z=>E z∧
      OrdinaryInducedRimCutEvent I
        (sampledOrientation (rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) z.2) α pstar):=by
  obtain ⟨N,hN⟩:=ordinary_expanded_induced_rim_cut_with_prior α pstar hα hα1 hpstar q₀
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P I hn density hthreshold hmin p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum hpstarR
    d hd q hq hQ s hs hS R _ ρ E a μ ν hE
  have hparent := ordinary_induced_parent_threshold_from_density P I density α hthreshold hmin
  have hhalf : (1/2 : ℝ) ≤ cycleThreshold 3 := cycleThreshold_half_le (by omega)
  have hcoef : (1/2 : ℝ) + α ≤ cycleThreshold 3 + α := by linarith
  have hdegree : ∀ v : I, (1/2 + α) * I.card ≤ ((P.induce (I : Set V)).degree v : ℝ) := by
    intro v
    exact (mul_le_mul_of_nonneg_right hcoef (by positivity : (0 : ℝ) ≤ I.card)).trans (hparent v)
  exact hN V U Γ Color P I hn hdegree p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum hpstarR
    d hd q hq hQ s hs hS ρ E a hE
end Oberwolfach
