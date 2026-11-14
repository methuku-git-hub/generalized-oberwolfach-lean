module

public import Oberwolfach.FiniteProjectedProductEvent
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

theorem ordinary_expanded_induced_rim_cut_with_prior
    (α pstar:ℝ) (hα:0<α) (hα1:α≤1/2) (hpstar:0<pstar) (q₀:ℕ):
    ∃N:ℕ,∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀(P:SimpleGraph V) (I:Finset V),N≤I.card→
      (∀v:I,(1/2+α)*I.card≤((P.induce (I:Set V)).degree v:ℝ))→
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
  obtain ⟨N,hN⟩:=ordinary_induced_rim_cut_high_probability α pstar hα hα1 hpstar q₀
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P I hn hP p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum hpstarR
    d hd q hq hQ s hs hS R _ ρ E a μ ν hE
  let μraw:=FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>2*p) (fun _=>by linarith) (fun _=>by linarith) d hd q hq hQ s hs hS)
  let f:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→RawWheelOutcome V U Γ Color:=
    fun σ e=>expandedOrdinarySelectedCollapse e (σ e)
  have hproj:(μ.sigma ρ).map (fun z=>f z.1)=μraw:=by
    calc
      _ = ((μ.sigma ρ).map Sigma.fst).map f:=by rw [finiteLaw_map_map]
      _ = μ.map f:=by rw [finiteLaw_sigma_map_first_dependent]
      _ = μraw:=expanded_ordinary_selected_wheel_law p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS
  have hraw:=hN V U Γ Color P I hn hP (2*p) (by linarith) (by linarith) hpstarR d hd q hq hQ s hs hS
  have hA:1-1/(I.card:ℝ)^q₀≤(μraw.prod ν).probability (fun z=>
      OrdinaryInducedRimCutEvent I (sampledOrientation (rawWheelGraph P z.1) z.2) α pstar):=by
    convert hraw using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  exact finite_projected_product_event (μ.sigma ρ) μraw ν (fun z=>f z.1) hproj E
    (fun z=>OrdinaryInducedRimCutEvent I (sampledOrientation (rawWheelGraph P z.1) z.2) α pstar)
    a (1/(I.card:ℝ)^q₀) hE hA
end Oberwolfach
