module

public import Oberwolfach.ExpandedOrdinarySampledHubTotals
public import Oberwolfach.FiniteSeedFailureMargins

@[expose] public section
/-! Uniform high-probability control of the full ordinary candidate weight
at every hub, at linear error scale. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem expanded_ordinary_hub_totals_high
    (d m:ℕ) (hd:2≤d) (hm:2≤m) (B η ζ:ℝ) (hB:0<B) (hη:0<η) (hζ:0<ζ):
    ∃N:ℕ,1≤N ∧ ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
    N≤Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀(P:SimpleGraph V) (π:Equiv.Perm V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j ≤ intervalUncoveredProbability d (∑g,q w g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (w:OrderedOrdinaryWheel (U:=U) π (3*d) (m+1)→ℝ)
    (hw:∀W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m) (g:Γ) (j:Color)
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-ζ≤(μ.sigma ν).probability (fun z=>∀hub,
      |orderedOrdinarySampledHubTotal P π d m w g j hub (fun e=>rawExpandedApproximateCollapse e (z.1 e))-
       ∑W,orderedOrdinaryHubWeight w hub W *
        ∏a∈orderedOrdinaryResources W,rawMarkedWheelMarginal P π d p₂ k₂ q s g j (orderedOrdinaryResourceEmbedding a)|<η*Fintype.card V) :=by
  let C:=((m:ℝ)+1)^2*B
  let D:ℝ:=(8*(d:ℝ)+6)^2*C*(2*((m:ℝ)+1))*C
  have hD:0<D:=by dsimp [D,C];positivity
  obtain ⟨N,hN⟩:=eventually_any_polynomial_exponential_failure_below 2 (2*η^2/D) ζ 1 (by positivity) hζ
  refine ⟨max 1 N,by omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn huV P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort w hw g j R _ ν μ
  have hnpos:0<Fintype.card V:=by omega
  have hnR:0<(Fintype.card V:ℝ):=by exact_mod_cast hnpos
  have huR:(Fintype.card U:ℝ)≤Fintype.card V:=by exact_mod_cast huV
  have hEq:-2*(η*(Fintype.card V:ℝ))^2/
      ((8*(d:ℝ)+6)^2*C*(2*((m:ℝ)+1))*((Fintype.card V:ℝ)*C))=
      -(2*η^2/D)*(Fintype.card V:ℝ):=by
    dsimp [D]
    field_simp
    <;> ring
  have hfail:2*(Fintype.card V:ℝ)*Real.exp (-(2*η^2/D)*(Fintype.card V:ℝ))<ζ:=by
    simpa only [pow_one] using hN (Fintype.card V) (by omega)
  have hcard:(Fintype.card U:ℝ)*(2*Real.exp (-(2*η^2/D)*(Fintype.card V:ℝ)))≤
      2*(Fintype.card V:ℝ)*Real.exp (-(2*η^2/D)*(Fintype.card V:ℝ)):=by
    nlinarith [mul_le_mul_of_nonneg_right huR (show 0≤2*Real.exp (-(2*η^2/D)*(Fintype.card V:ℝ)) by positivity)]
  have hh:=expanded_ordinary_sampled_hub_totals P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS hnoshort m hm hnpos huV w B hB hw g j (η*(Fintype.card V:ℝ)) (by positivity) ν
  dsimp only at hh
  rw [←show C=((m:ℝ)+1)^2*B from rfl,hEq] at hh
  have hnum:1-ζ≤1-(Fintype.card U:ℝ)*
      (2*Real.exp (-(2*η^2/D)*(Fintype.card V:ℝ))):=by linarith
  exact hnum.trans hh
end Oberwolfach
