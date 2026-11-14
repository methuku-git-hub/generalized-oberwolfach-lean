module

public import Oberwolfach.OrdinaryExpandedVortexTestsAttach

@[expose] public section
/-! Attach an arbitrary reference event and all fixed-vortex row and hub tests to an
arbitrary prior event on exactly the same expanded sample and second stage. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_expanded_attach_vortex_rows_reference
    (h d:ℕ) (hd:2≤d) (εR εH β ε ρ₀ χ:ℝ)
    (hεR:0<εR) (hεH:0<εH) (hβ:0≤β) (hβ1:β≤1/4)
    (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hχ:0<χ):
    ∃m₀:ℕ,1≤m₀ ∧ ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀(P:SimpleGraph V) (D m:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤m→
    ∀(Q:Vortex U P D β ε m) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      (∀x k,0<k→k<2*d+1→(π^k) x≠x)→
    ∀(p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
      (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
      (s:U→Color→ℝ) (hs:∀w j,0≤s w j)
      (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g)) (j:Color) (pH:ℝ) (hj:∀w,s w j=pH),
    ∀(A:RawWheelOutcome V U Γ Color→Prop) (εA:ℝ),
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
      (E:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)→Prop) (εE:ℝ),
    let hp2:0≤2*p:=by positivity;
    let hp21:2*p≤1:=by linarith;
    1-εA≤(FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>2*p) (fun _=>hp2) (fun _=>hp21)
      d hd q hq hQ s hs hS)).probability A→
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-εE≤(μ.sigma ν).probability E→
    1-((εE+χ)+εA)≤(μ.sigma ν).probability (fun z=>
      (E z ∧ OrdinaryFixedVortexRowIndexEvent h d εR εH P (permutationConflictGraph π (3*d))
        D m β ε Q π hπ (2*p) pH s j (fun e=>expandedOrdinarySelectedCollapse e (z.1 e))) ∧
      A (fun e=>expandedOrdinarySelectedCollapse e (z.1 e))):=by
  obtain ⟨m₀,hm₀,hattach⟩:=ordinary_expanded_attach_fixed_vortex_tests h d hd εR εH β ε ρ₀ χ
    hεR hεH hβ hβ1 hε hε1 hρ₀ hχ
  refine ⟨m₀,hm₀,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D m hreg hn hD hρlo hρhi hm Q π hπ hnoshort
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS j pH hj A εA R _ ν E εE
    hp2 hp21 hA μ hE
  have hRows:=hattach V U Γ Color P (permutationConflictGraph π (3*d)) D m hreg hn hD hρlo hρhi hm Q π hπ hnoshort le_rfl
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS j pH hj ν E εE hE
  let E':(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)→Prop:=fun z=>
    E z ∧ OrdinaryFixedVortexRowIndexEvent h d εR εH P (permutationConflictGraph π (3*d))
      D m β ε Q π hπ (2*p) pH s j (fun e=>expandedOrdinarySelectedCollapse e (z.1 e))
  have hRows':1-(εE+χ)≤(μ.sigma ν).probability E':=by exact hRows
  exact ordinary_expanded_add_general_reference_event p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS ν
    A E' εA (εE+χ) hA hRows'
end Oberwolfach
