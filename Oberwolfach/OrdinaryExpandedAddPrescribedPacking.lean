module

public import Oberwolfach.OrdinaryPrescribedPackingEvent
public import Oberwolfach.OrdinaryExpandedAddReferenceEvent

@[expose] public section
/-! Add adaptive prescribed-edge wheel packing to an already combined event
on the same expanded sample, including dependent second-stage choices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
theorem ordinary_expanded_add_prescribed_packing (r:ℕ) (hr:3≤r) (p₀ γ ω K₀:ℝ)
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
    (E:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)→Prop) (εE:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) (pR/2) 0 (p₂/2) 0 u
      (by positivity) (by norm_num) (by positivity) (by norm_num) hu (by linarith) d hd q hq hQ s hs hS);
    1-εE≤(μ.sigma ν).probability E →
    1-(εE+1/(A.card:ℝ)^q₀)≤(μ.sigma ν).probability (fun z=>
      E z ∧ OrdinaryPrescribedPackingEvent r d p₀ γ α P F π A U₀ j
        (fun e=>expandedOrdinarySelectedCollapse e (z.1 e))) :=by
  obtain ⟨α₀,hα₀,hα₁,hpack⟩:=prescribed_inner_packing_common_event r hr p₀ γ ω K₀ hp₀ hp₀1 hγ hγ1 hω hK₀
  refine ⟨α₀,hα₀,hα₁,?_⟩
  intro α L hα hαsmall hL d q₀ hd
  obtain ⟨N,hN⟩:=hpack α L hα hαsmall hL d q₀ hd
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P F π A U₀ hn hV hU hωU hFπ hF hdeg hnoshort
    pR pH hpR hpR1 hpR0 hpH0 q hq hQ s hs hS j hj p₂ u ρ hp₂ hu hρ hsum R _ ν E εE μ hE
  have hPacked:=hN V U Γ Color P F π A U₀ hn hV hU hωU hFπ hF hdeg hnoshort
    pR pH hpR hpR1 hpR0 hpH0 q hq hQ s hs hS j hj
  have hNamed:1-1/(A.card:ℝ)^q₀≤(FiniteLaw.pi (rawWheelLaw (fun _=>pR) (fun _=>hpR) (fun _=>hpR1) d hd q hq hQ s hs hS)).probability
      (OrdinaryPrescribedPackingEvent r d p₀ γ α P F π A U₀ j):=by
    exact hPacked
  exact ordinary_expanded_add_reference_event pR p₂ u ρ hpR hp₂ hu hρ hsum d hd q hq hQ s hs hS ν
    (OrdinaryPrescribedPackingEvent r d p₀ γ α P F π A U₀ j) E (1/(A.card:ℝ)^q₀) εE hNamed hE
end Oberwolfach
