module

public import Oberwolfach.OrdinaryPrescribedPackingEvent
public import Oberwolfach.OrdinaryExpandedSharedSampleEvents

@[expose] public section
/-! Combine adaptive prescribed-edge wheel packing with a reference event and
an arbitrary full-class event on the same expanded sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
theorem ordinary_expanded_prescribed_packing_shared (r:ℕ) (hr:3≤r) (p₀ γ ω K₀:ℝ)
    (hp₀:0<p₀) (hp₀1:p₀≤1) (hγ:0<γ) (hγ1:γ≤1) (hω:0<ω) (hK₀:1≤K₀):
    ∃ α₀:ℝ,0<α₀ ∧ α₀≤1 ∧ ∀ α L:ℝ,0<α → α≤α₀ → 0≤L →
    ∀ d q₀:ℕ,∀ hd:2≤d,∃ N:ℕ,
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀ (P F:SimpleGraph V) (π:Equiv.Perm V) (A:Finset V) (U₀:Finset U),N≤A.card →
      (Fintype.card V:ℝ)≤K₀*A.card → (Fintype.card U:ℝ)≤K₀*A.card → ω*A.card≤(U₀.card:ℝ) →
      permutationConflictGraph π (3*d)≤F → (∀ v,(F.degree v:ℝ)≤L) →
      (∀ v,(1/2+γ)*A.card≤((A∩P.neighborFinset v).card:ℝ)) →
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ (pR pH:ℝ) (hpR:0≤pR) (hpR1:pR≤1),p₀≤pR → p₀≤pH →
    ∀ (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (j:Color),(∀ u,s u j=pH) →
    ∀(p₂ u ρ:ℝ) (hp₂:0≤p₂) (hu:0≤u) (hρ:ρ≤1) (hsum:pR+p₂+u=ρ)
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (Host:RawWheelOutcome V U Γ Color→Prop) (Good:SimpleGraph V→Prop) (εHost εGood:ℝ),
    1-εHost≤(FiniteLaw.pi (rawWheelLaw (fun _=>pR) (fun _=>hpR) (fun _=>hpR1) d hd q hq hQ s hs hS)).probability Host →
    1-εGood≤(FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.retentionCoin ρ (by linarith) hρ)).probability (fun σ=>Good (retainedGraph P σ)) →
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) (pR/2) 0 (p₂/2) 0 u
      (by positivity) (by norm_num) (by positivity) (by norm_num) hu (by linarith) d hd q hq hQ s hs hS);
    1-(εHost+1/(A.card:ℝ)^q₀+εGood)≤(μ.sigma ν).probability (fun z=>
      Host (fun e=>expandedOrdinarySelectedCollapse e (z.1 e)) ∧
      OrdinaryPrescribedPackingEvent r d p₀ γ α P F π A U₀ j (fun e=>expandedOrdinarySelectedCollapse e (z.1 e)) ∧
      Good (longPhysicalStateGraph P z.1 {0,1,2,3,4})) :=by
  obtain ⟨α₀,hα₀,hα₁,hpack⟩:=prescribed_inner_packing_common_event r hr p₀ γ ω K₀ hp₀ hp₀1 hγ hγ1 hω hK₀
  refine ⟨α₀,hα₀,hα₁,?_⟩
  intro α L hα hαsmall hL d q₀ hd
  obtain ⟨N,hN⟩:=hpack α L hα hαsmall hL d q₀ hd
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P F π A U₀ hn hV hU hωU hFπ hF hdeg hnoshort
    pR pH hpR hpR1 hpR0 hpH0 q hq hQ s hs hS j hj p₂ u ρ hp₂ hu hρ hsum R _ ν Host Good εHost εGood hHost hGood
  have hPacked:=hN V U Γ Color P F π A U₀ hn hV hU hωU hFπ hF hdeg hnoshort
    pR pH hpR hpR1 hpR0 hpH0 q hq hQ s hs hS j hj
  have hNamed:1-1/(A.card:ℝ)^q₀≤(FiniteLaw.pi (rawWheelLaw (fun _=>pR) (fun _=>hpR) (fun _=>hpR1) d hd q hq hQ s hs hS)).probability
      (OrdinaryPrescribedPackingEvent r d p₀ γ α P F π A U₀ j):=by
    exact hPacked
  have hBoth:=finiteLaw_intersection_lower (FiniteLaw.pi (rawWheelLaw (fun _=>pR) (fun _=>hpR) (fun _=>hpR1) d hd q hq hQ s hs hS))
    Host (OrdinaryPrescribedPackingEvent r d p₀ γ α P F π A U₀ j) εHost (1/(A.card:ℝ)^q₀) hHost hNamed
  have hBoth':1-(εHost+1/(A.card:ℝ)^q₀)≤(FiniteLaw.pi (rawWheelLaw (fun _=>pR) (fun _=>hpR) (fun _=>hpR1) d hd q hq hQ s hs hS)).probability
      (fun σ=>Host σ ∧ OrdinaryPrescribedPackingEvent r d p₀ γ α P F π A U₀ j σ):=by
    simpa only [sub_add_eq_sub_sub] using hBoth
  simpa only [and_assoc] using ordinary_expanded_shared_sample_events P pR p₂ u ρ hpR hp₂ hu hρ hsum d hd q hq hQ s hs hS ν
    (fun σ=>Host σ ∧ OrdinaryPrescribedPackingEvent r d p₀ γ α P F π A U₀ j σ) Good
    (εHost+1/(A.card:ℝ)^q₀) εGood hBoth' hGood
end Oberwolfach
