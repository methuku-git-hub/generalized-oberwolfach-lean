module

public import Oberwolfach.OrdinaryExpandedVortexDeepRowsAttach

@[expose] public section
/-! A prior expanded-sample event, all-level robust deep cover and all-level
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

theorem ordinary_expanded_vortex_deep_rows_regular
    (mDeep:ℕ) (hm:3≤mDeep) (α ρ₀ pmin:ℝ) (hα:0<α) (hρ₀:0<ρ₀) (hpmin:0<pmin) (hpmin1:pmin≤1):
    ∃K:ℕ,0<K ∧ ∃a ε₀ ρ θdeep:ℝ,0<a ∧ 0<ε₀ ∧ 0<ρ ∧ 0<θdeep ∧
    ∀(ε χdeep:ℝ),0<ε→ε<1/4→ε≤a→ε≤ρ₀/16→0<χdeep→
    ∀(β:ℝ),0≤β→β≤1/4→β≤α/8→β≤ε₀→
    ∀(εR εH χrows:ℝ),0<εR→0<εH→0<χrows→
    ∀aLoad:ℝ,0<aLoad→aLoad≤a→∀d:ℕ,∀hd:2≤d,∃v₀:ℕ,1≤v₀ ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀(P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      (∀x k,0<k→k<2*d+1→(π^k) x≠x)→
    ∀(θhost:ℝ),1/2≤θhost→cycleThreshold (mDeep+1)≤θhost→
      (θhost+α)*Fintype.card V≤D→
    ∀(p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
      (pH:ℝ),pmin≤2*p→pmin≤pH→pH≤1→2*p=initialIndexDensity U D*pH→
    ∀(q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
      (s:U→Color→ℝ) (hs:∀w j,0≤s w j)
      (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g)) (j:Color) (hj:∀w,s w j=pH),
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
      (E:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)→Prop) (εE:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-εE≤(μ.sigma ν).probability E→
    1-((εE+χrows)+χdeep)≤(μ.sigma ν).probability (fun z=>
      (E z ∧ OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d))
        D vsize β ε Q π hπ (2*p) pH s j (fun e=>expandedOrdinarySelectedCollapse e (z.1 e))) ∧
      OrdinaryFixedVortexDeepCoverEvent mDeep K d a aLoad ρ θdeep P D vsize β ε Q π hπ j
        (fun e=>expandedOrdinarySelectedCollapse e (z.1 e))):=by
  obtain ⟨K,hK,a,ε₀,ρ,θdeep,ha,hε₀,hρ,hθ,hdeep⟩:=
    ordinary_fixed_vortex_deep_cover_common mDeep hm α ρ₀ pmin hα hρ₀ hpmin hpmin1
  refine ⟨K,hK,a,ε₀,ρ,θdeep,ha,hε₀,hρ,hθ,?_⟩
  intro ε χdeep hε hε1 hεa hεsmall hχdeep β hβ hβ1 hβα hβε εR εH χrows hεR hεH hχrows
    aLoad hload hloadA d hd
  obtain ⟨vDeep,hvDeep,hdeep⟩:=hdeep ε χdeep hε hε1 hεa hεsmall hχdeep β hβ hβ1 hβα hβε aLoad hload hloadA d hd
  obtain ⟨vRows,hvRows,hrows⟩:=ordinary_expanded_attach_vortex_deep_rows 3 d hd εR εH β ε ρ₀ χrows
    hεR hεH hβ hβ1 hε hε1 hρ₀ hχrows
  refine ⟨max vDeep vRows,by omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D vsize hreg hn hρlo hρhi hv Q π hπ hnoshort θhost hθ hthreshold hdegree
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpRlo hpHlo hpH1 hpEq q hq hQ s hs hS j hj R _ ν E εE μ hE
  have hDhalf:(Fintype.card V:ℝ)/2≤D:=by
    have hh:=mul_le_mul_of_nonneg_right (show (1/2:ℝ)≤θhost+α by linarith) (show (0:ℝ)≤Fintype.card V by positivity)
    nlinarith only [hh,hdegree]
  have hpR1:2*p≤1:=by linarith
  have hDeep:=hdeep V U Γ Color P D vsize hreg hn hρlo hρhi (by omega) Q π hπ hnoshort θhost hθ hthreshold hdegree
    (2*p) pH hpRlo hpR1 hpHlo hpH1 hpEq q hq hQ s hs hS j hj
  have hp2:0≤2*p:=by positivity
  have hDeep':1-χdeep≤(FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>2*p) (fun _=>hp2) (fun _=>hpR1)
      d hd q hq hQ s hs hS)).probability
      (OrdinaryFixedVortexDeepCoverEvent mDeep K d a aLoad ρ θdeep P D vsize β ε Q π hπ j):=by
    exact hDeep
  exact hrows V U Γ Color P D vsize hreg hn hDhalf hρlo hρhi (by omega) Q π hπ hnoshort
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS j pH hj mDeep K a aLoad ρ θdeep χdeep ν E εE hDeep' hE
end Oberwolfach
