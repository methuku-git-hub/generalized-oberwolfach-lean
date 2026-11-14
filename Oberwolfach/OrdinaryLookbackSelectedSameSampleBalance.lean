module

public import Oberwolfach.VortexLookbackPermutation
public import Oberwolfach.OrdinaryExpandedThreeStepVortexBalanceAttach

@[expose] public section
/-! The strengthened vortex and preserving permutation can be selected before
sampling, and the deeper balance is attached to any later event on that sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_lookback_selected_same_sample_balance
    (d:ℕ) (hd:2≤d) (εR εH β ε ρ₀ χ:ℝ)
    (hεR:0<εR) (hεH:0<εH) (hβ:0<β) (hβ1:β≤1/4)
    (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hχ:0<χ):
    ∃m₀:ℕ,1≤m₀ ∧ ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀(P:SimpleGraph V) (D m:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤m→m≤Fintype.card V→
    ∃(Q:VortexLookback U P D β ε m 2) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.toVortex.extendedVertices i↔x∈Q.toVortex.extendedVertices i),
      (∀x k,0<k→k<2*d+1→(π^k) x≠x) ∧
    ∀(p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
      (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
      (s:U→Color→ℝ) (hs:∀w j,0≤s w j)
      (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g)) (j:Color) (pH:ℝ)
      (hj:∀w,s w j=pH) (hpH:0≤pH) (hbalance:2*p=initialIndexDensity U D*pH),
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
      (E:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)→Prop) (εE:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-εE≤(μ.sigma ν).probability E→
    1-(εE+χ)≤(μ.sigma ν).probability (fun z=>E z ∧
      OrdinaryVortexThreeStepRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d)) D m β ε
        Q.toVortex π hπ (2*p) pH s j (fun e=>expandedOrdinarySelectedCollapse e (z.1 e)) ∧
      OrdinaryVortexThreeStepEditedBalanceEvent P D m β ε pH εR εH Q π hπ d j
        (fun e=>expandedOrdinarySelectedCollapse e (z.1 e))):=by
  obtain ⟨m₁,hm₁,hvortex⟩:=vortex_lookback_with_permutation_exists hβ hε hε1 hρ₀ 2 (2*d+1) (by omega)
  obtain ⟨m₂,hm₂,hattach⟩:=ordinary_expanded_attach_three_step_vortex_balance d hd εR εH β ε ρ₀ χ
    hεR hεH hβ.le hβ1 hε hε1 hρ₀ hχ
  refine ⟨max m₁ m₂,by omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D m hreg hn hD hρlo hρhi hm hmn
  obtain ⟨Q,π,hπ,hshort⟩:=hvortex V U P D m hreg hD hρlo hρhi (by omega) hmn
  refine ⟨Q,π,hπ,hshort,?_⟩
  intro p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS j pH hj hpH hbalance R _ ν E εE μ hE
  exact hattach V U Γ Color P (permutationConflictGraph π (3*d)) D m hreg hn hD hρlo hρhi (by omega)
    Q π hπ hshort le_rfl p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS j pH hj hpH hbalance ν E εE hE
end Oberwolfach
