module

public import Oberwolfach.ExpandedOrdinaryHubTotalsHigh
public import Oberwolfach.FiniteHighEventsCommon

@[expose] public section
/-! Every fixed ordinary candidate length has its full weight concentrated
at every hub on the same expanded sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem expanded_ordinary_hub_total_family
    (I:Type) [Fintype I] (d:ℕ) (hd:2≤d) (m:I→ℕ) (hm:∀i,2≤m i)
    (B η:I→ℝ) (hB:∀i,0<B i) (hη:∀i,0<η i) (ζ:ℝ) (hζ:0<ζ):
    ∃N:ℕ,1≤N ∧ ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
    N≤Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀(P:SimpleGraph V) (π:Equiv.Perm V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j ≤ intervalUncoveredProbability d (∑g,q w g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (w:∀i,OrderedOrdinaryWheel (U:=U) π (3*d) (m i+1)→ℝ)
    (hw:∀i W,0≤w i W ∧ w i W≤B i/(Fintype.card V:ℝ)^(m i)) (g:I→Γ) (j:I→Color)
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-ζ≤(μ.sigma ν).probability (fun z=>∀i hub,
      |orderedOrdinarySampledHubTotal P π d (m i) (w i) (g i) (j i) hub (fun e=>rawExpandedApproximateCollapse e (z.1 e))-
       ∑W,orderedOrdinaryHubWeight (w i) hub W *
        ∏a∈orderedOrdinaryResources W,rawMarkedWheelMarginal P π d p₂ k₂ q s (g i) (j i) (orderedOrdinaryResourceEmbedding a)|<η i*Fintype.card V) :=by
  let ε:ℝ:=ζ/((Fintype.card I:ℝ)+1)
  have hε:0<ε:=by dsimp [ε];positivity
  have hex:∀i,∃N:ℕ,1≤N ∧ ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
      N≤Fintype.card V→Fintype.card U≤Fintype.card V→
      ∀(P:SimpleGraph V) (π:Equiv.Perm V)
      (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
      (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
      (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j ≤ intervalUncoveredProbability d (∑g,q w g))
      (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
      (w:OrderedOrdinaryWheel (U:=U) π (3*d) (m i+1)→ℝ)
      (hw:∀W,0≤w W ∧ w W≤B i/(Fintype.card V:ℝ)^(m i)) (g:Γ) (j:Color)
      {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)),
      let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
      1-ε≤(μ.sigma ν).probability (fun z=>∀hub,
        |orderedOrdinarySampledHubTotal P π d (m i) w g j hub (fun e=>rawExpandedApproximateCollapse e (z.1 e))-
         ∑W,orderedOrdinaryHubWeight w hub W *
          ∏a∈orderedOrdinaryResources W,rawMarkedWheelMarginal P π d p₂ k₂ q s g j (orderedOrdinaryResourceEmbedding a)|<η i*Fintype.card V):=by
    intro i
    exact expanded_ordinary_hub_totals_high d (m i) hd (hm i) (B i) (η i) ε (hB i) (hη i) hε
  choose Ni hNi using hex
  refine ⟨max 1 (Finset.univ.sup Ni),by omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn huV P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort w hw g j R _ ν μ
  let law:=μ.sigma ν
  let E:=fun (i:I) (z:Σσ:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e),R σ)=>∀hub,
      |orderedOrdinarySampledHubTotal P π d (m i) (w i) (g i) (j i) hub (fun e=>rawExpandedApproximateCollapse e (z.1 e))-
       ∑W,orderedOrdinaryHubWeight (w i) hub W *
        ∏a∈orderedOrdinaryResources W,rawMarkedWheelMarginal P π d p₂ k₂ q s (g i) (j i) (orderedOrdinaryResourceEmbedding a)|<η i*Fintype.card V
  have hi:∀i∈(Finset.univ:Finset I),1-ε≤law.probability (E i):=by
    intro i _
    exact (hNi i).2 V U Γ Color (by have hh:Ni i≤Finset.univ.sup Ni:=Finset.le_sup (Finset.mem_univ i);omega) huV P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort (w i) (hw i) (g i) (j i) ν
  have hh:=finiteLaw_high_events_common law (Finset.univ:Finset I) E (fun _=>ε) hi
  have hbudget:(∑_i:I,ε)≤ζ:=by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    dsimp [ε]
    have hcard:(0:ℝ)≤Fintype.card I:=by positivity
    have hden:0<((Fintype.card I:ℝ)+1):=by positivity
    rw [←mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hnum:1-ζ≤1-∑_i:I,ε:=by linarith
  change 1-ζ≤law.probability (fun z=>∀i,E i z)
  have hh':1-∑_i:I,ε≤law.probability (fun z=>∀i,E i z):=by
    simpa only [Finset.mem_univ,true_implies] using hh
  exact hnum.trans hh'
end Oberwolfach
