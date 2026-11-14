module

public import Oberwolfach.FiniteLawPositiveEventWitness
public import Oberwolfach.OrdinaryFixedVortexTriangleSeparateLoadFineCoverEvent
public import Oberwolfach.OrdinaryFixedVortexTriangleSeparateLoadFineCoverCapped
public import Oberwolfach.OrdinaryExpandedRawEventProductPrior

@[expose] public section
/-! A prior expanded-sample event, all-level triangle cover and all-level
row and hub tests occur together, with the local host hypotheses derived from
the original regular host and its vortex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_expanded_vortex_triangle_separate_load_fine_supported_product_prior_capped
    (α ρ₀ pmin cap:ℝ) (hα:0<α) (hρ₀:0<ρ₀) (hpmin:0<pmin) (hpmin1:pmin≤1) (hcap:0<cap):
    ∃κ:ℝ,0<κ ∧ κ≤1 ∧ κ≤cap ∧ ∀aLoad:ℝ,0<aLoad→aLoad≤κ→∀(ε χdeep:ℝ),0<ε→ε<1/4→ε≤κ→ε≤ρ₀/16→0<χdeep→
    ∀(β:ℝ),0≤β→β≤1/4→β≤α/8→β≤κ→
    ∀d:ℕ,∀hd:2≤d,∃v₀:ℕ,1≤v₀ ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U],
    ∀(P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      (∀x k,0<k→k<2*d+1→(π^k) x≠x)→
    ∀(θhost:ℝ),1/2≤θhost→cycleThreshold 3≤θhost→
      (θhost+α)*Fintype.card V≤D→
    ∀(p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
      (pH:ℝ),pmin≤2*p→pmin≤pH→pH≤1→2*p=initialIndexDensity U D*pH→
    ∀(q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
      (s:U→Color→ℝ) (hs:∀w j,0≤s w j)
      (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g)) (j:Color) (hj:∀w,s w j=pH),
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
      (νcoins:FiniteLaw (Sym2 V→Bool))
      (E:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)×(Sym2 V→Bool)→Prop) (εE:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-εE≤((μ.sigma ν).prod νcoins).probability E→
    let All:=fun z=>E z ∧ OrdinaryFixedVortexTriangleSeparateLoadFineCoverEvent d κ aLoad P D vsize β ε Q π hπ j
        (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e));
    1-(εE+χdeep)≤((μ.sigma ν).prod νcoins).probability All ∧
      (0<1-(εE+χdeep)→∃z,0<((μ.sigma ν).prod νcoins).mass z ∧ All z):=by
  obtain ⟨κ,hκ,hκ1,hκcap,hdeep⟩:=ordinary_fixed_vortex_triangle_separate_load_fine_cover_capped α ρ₀ pmin cap hα hρ₀ hpmin hpmin1 hcap
  refine ⟨κ,hκ,hκ1,hκcap,?_⟩
  intro aLoad haLoad haLoadκ ε χdeep hε hε1 hεa hεsmall hχdeep β hβ hβ1 hβα hβε d hd
  obtain ⟨vDeep,hvDeep,hdeep⟩:=hdeep aLoad haLoad haLoadκ ε χdeep hε hε1 hεa hεsmall hχdeep β hβ hβ1 hβα hβε d hd
  refine ⟨vDeep,hvDeep,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D vsize hreg hn hρlo hρhi hv Q π hπ hnoshort θhost hθ hthreshold hdegree
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpRlo hpHlo hpH1 hpEq q hq hQ s hs hS j hj R _ ν νcoins E εE μ hE All
  have hpR1:2*p≤1:=by linarith
  have hDeep:=hdeep V U Γ Color P D vsize hreg hn hρlo hρhi (by omega) Q π hπ hnoshort θhost hθ hthreshold hdegree
    (2*p) pH hpRlo hpR1 hpHlo hpH1 hpEq q hq hQ s hs hS j hj
  have hp2:0≤2*p:=by positivity
  have hDeep':1-χdeep≤(FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>2*p) (fun _=>hp2) (fun _=>hpR1)
      d hd q hq hQ s hs hS)).probability
      (OrdinaryFixedVortexTriangleSeparateLoadFineCoverEvent d κ aLoad P D vsize β ε Q π hπ j):=by
    exact hDeep
  have hh:=ordinary_expanded_add_raw_event_with_product_prior p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS ν νcoins E
    (OrdinaryFixedVortexTriangleSeparateLoadFineCoverEvent d κ aLoad P D vsize β ε Q π hπ j) εE χdeep hE hDeep'
  have hlower:1-(εE+χdeep)≤((μ.sigma ν).prod νcoins).probability All:=by
    dsimp [All]
    linarith only [hh]
  refine ⟨hlower,?_⟩
  intro hpos
  exact finiteLaw_positive_mass_witness_of_event ((μ.sigma ν).prod νcoins) All (lt_of_lt_of_le hpos hlower)
end Oberwolfach
