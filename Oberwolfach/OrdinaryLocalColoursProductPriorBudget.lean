module

public import Oberwolfach.OrdinaryLocalColoursProductPrior
public import Oberwolfach.OrdinaryLocalColourFailureBudget

@[expose] public section
/-! Local colour estimates retain a prior product event within any fixed
positive additional probability budget. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem ordinary_local_colours_product_prior_budget
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (A:Finset V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (κ:FiniteLaw (Sym2 V→Bool))
    (E:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)×(Sym2 V→Bool)→Prop)
    (loss ζ χ:ℝ) (hζ:0<ζ) (hχ:0<χ):
    ∃N:ℕ,1≤N ∧ (N≤A.card→
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-loss≤((μ.sigma ν).prod κ).probability E→
    1-χ-loss≤((μ.sigma ν).prod κ).probability (fun z=>
      (∀a:Fin 6,∀x∈A,
        |(((P.neighborFinset x∩A).filter (fun y=>(z.1.1 (Sum.inl s(x,y))).1=a)).card:ℝ)-
          markedExpandedPhysicalProbability p k p₂ k₂ u a*(P.neighborFinset x∩A).card|<ζ*A.card) ∧ E z)) :=by
  obtain ⟨N,hN,hfail⟩:=ordinary_local_colour_failure_budget ζ χ hζ hχ
  refine ⟨N,hN,?_⟩
  intro hsize μ hE
  have hA:0<(A.card:ℝ):=by exact_mod_cast (show 0<A.card by omega)
  have ht:0<ζ*(A.card:ℝ):=mul_pos hζ hA
  have hh:=ordinary_local_colours_product_prior P A A p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS ν κ E loss (ζ*A.card) ht hE
  have hsmall:=hfail A.card hsize
  linarith
end Oberwolfach
