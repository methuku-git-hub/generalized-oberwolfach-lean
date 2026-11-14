module

public import Oberwolfach.FiniteProjectedProductEvent
public import Oberwolfach.ExpandedOrdinarySelectedLaw
public import Oberwolfach.FiniteSigmaFirstMap
public import Oberwolfach.FiniteLawProductMap

@[expose] public section
/-! Preserve an arbitrary expanded-sample event while adding both a raw
reference event and an event using the same raw outcome and direction coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_expanded_add_raw_and_coin_events
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq V] [DecidableEq U]
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ))
    (E:(Σσ,R σ)×(Sym2 V→Bool)→Prop) (A:RawWheelOutcome V U Γ Color→Prop)
    (B:RawWheelOutcome V U Γ Color×(Sym2 V→Bool)→Prop) (εE εA εB:ℝ):
    let μraw:=FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>2*p) (fun _=>by linarith) (fun _=>by linarith) d hd q hq hQ s hs hS)
    let ν:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.fairCoin)
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-εA≤μraw.probability A→1-εB≤(μraw.prod ν).probability B→
    1-εE≤((μ.sigma ρ).prod ν).probability E→
    1-((εE+εA)+εB)≤((μ.sigma ρ).prod ν).probability (fun z=>
      (E z ∧ A (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
      B (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e),z.2)) :=by
  intro μraw ν μ hA hB hE
  let f:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→RawWheelOutcome V U Γ Color:=
    fun σ e=>expandedOrdinarySelectedCollapse e (σ e)
  have hproj:(μ.sigma ρ).map (fun z=>f z.1)=μraw:=by
    calc
      _ = ((μ.sigma ρ).map Sigma.fst).map f:=by rw [finiteLaw_map_map]
      _ = μ.map f:=by rw [finiteLaw_sigma_map_first_dependent]
      _ = μraw:=expanded_ordinary_selected_wheel_law p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS
  have hAprod:1-εA≤(μraw.prod ν).probability (fun z=>A z.1):=by
    rw [finiteLaw_prod_first_probability]
    exact hA
  have hfirst:=finite_projected_product_event (μ.sigma ρ) μraw ν (fun z=>f z.1) hproj E (fun z=>A z.1) εE εA hE hAprod
  have hfirst':1-(εE+εA)≤((μ.sigma ρ).prod ν).probability (fun z=>E z∧A (f z.1.1)):=by
    linarith only [hfirst]
  have hsecond:=finite_projected_product_event (μ.sigma ρ) μraw ν (fun z=>f z.1) hproj
    (fun z=>E z∧A (f z.1.1)) B (εE+εA) εB hfirst' hB
  simpa only [sub_add_eq_sub_sub,f] using hsecond
end Oberwolfach
