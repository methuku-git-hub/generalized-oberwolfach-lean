module

public import Oberwolfach.OrdinaryFixedVortexDeepCoverEvent
public import Oberwolfach.OrdinaryExpandedRawEventProductPrior

@[expose] public section
/-! The all-level separate-load cover for any long ordinary wheel can be
attached to an arbitrary prior on the same expanded sample and coin law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_expanded_general_deep_product_prior
    (m:ℕ) (hm:3≤m) (α ρ₀ pmin:ℝ) (hα:0<α) (hρ₀:0<ρ₀) (hp:0<pmin) (hp1:pmin≤1):
    ∃K:ℕ,0<K ∧ ∃a ε₀ ρ θdeep:ℝ,0<a ∧ 0<ε₀ ∧ 0<ρ ∧ 0<θdeep ∧
    ∀(ε χ:ℝ),0<ε→ε<1/4→ε≤a→ε≤ρ₀/16→0<χ→
    ∀β:ℝ,0≤β→β≤1/4→β≤α/8→β≤ε₀→
    ∀aLoad:ℝ,0<aLoad→aLoad≤a→∀d:ℕ,∀hd:2≤d,∃v₀:ℕ,1≤v₀ ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀(P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      (∀x l,0<l→l<2*d+1→(π^l) x≠x)→
    ∀(θhost p k p₂ k₂ u:ℝ) (hθ:1/2≤θhost) (hthreshold:cycleThreshold (m+1)≤θhost)
      (hdegree:(θhost+α)*Fintype.card V≤D)
      (hp0:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1),
    ∀(pH:ℝ),pmin≤2*p→pmin≤pH→pH≤1→2*p=initialIndexDensity U D*pH→
    ∀(q:U→Γ→ℝ) (hq:∀w z,0≤q w z) (hQ:∀w,∑z,q w z≤1/8)
      (s:U→Color→ℝ) (hs:∀w j,0≤s w j)
      (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑z,q w z)) (j:Color) (hj:∀w,s w j=pH),
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (νcoins:FiniteLaw (Sym2 V→Bool))
      (E:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)×(Sym2 V→Bool)→Prop) (loss:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp0 hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-loss≤((μ.sigma ν).prod νcoins).probability E→
    1-(loss+χ)≤((μ.sigma ν).prod νcoins).probability
      (fun z=>E z ∧ OrdinaryFixedVortexDeepCoverEvent m K d a aLoad ρ θdeep P D vsize β ε Q π hπ j
        (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) :=by
  obtain ⟨K,hK,a,ε₀,ρ,θdeep,ha,hε₀,hρ,hθ,hdeep⟩:=
    ordinary_fixed_vortex_deep_cover_common m hm α ρ₀ pmin hα hρ₀ hp hp1
  refine ⟨K,hK,a,ε₀,ρ,θdeep,ha,hε₀,hρ,hθ,?_⟩
  intro ε χ hε hε1 hεa hερ hχ β hβ hβ1 hβα hβε aLoad haLoad haLoadA d hd
  obtain ⟨v₀,hv₀,hdeep⟩:=hdeep ε χ hε hε1 hεa hερ hχ β hβ hβ1 hβα hβε aLoad haLoad haLoadA d hd
  refine ⟨v₀,hv₀,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D vsize hreg hn hρlo hρhi hv Q π hπ hnoshort
    θhost p k p₂ k₂ u hθ hthreshold hdegree hp0 hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq
    q hq hQ s hs hS j hj R _ ν νcoins E loss μ hE
  have hpR1:2*p≤1:=by linarith
  have hDeep:=hdeep V U Γ Color P D vsize hreg hn hρlo hρhi hv Q π hπ hnoshort θhost hθ hthreshold hdegree
    (2*p) pH hpR hpR1 hpH hpH1 hpEq q hq hQ s hs hS j hj
  have hDeep':1-χ≤(FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>2*p)
      (fun _=>(show 0≤2*p by positivity)) (fun _=>hpR1) d hd q hq hQ s hs hS)).probability
      (OrdinaryFixedVortexDeepCoverEvent m K d a aLoad ρ θdeep P D vsize β ε Q π hπ j):=by
    exact hDeep
  have hh:=ordinary_expanded_add_raw_event_with_product_prior p k p₂ k₂ u hp0 hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS ν νcoins E
    (OrdinaryFixedVortexDeepCoverEvent m K d a aLoad ρ θdeep P D vsize β ε Q π hπ j) loss χ hE hDeep'
  linarith only [hh]
end Oberwolfach
