module

public import Oberwolfach.PrescribedPackingFromRelativeCounts
public import Oberwolfach.OrdinaryDomainNeighbourhoodEvent
public import Oberwolfach.FixedHubDomainCounts

@[expose] public section

/-! One original-law event supplies every later prescribed-inner-edge
packing satisfying the explicit domain and size bounds. The excluded sets,
prescribed edges and bounded graph modifications may all depend on the
outcome. The counting domains and supplied marginals remain fixed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem prescribed_inner_packing_common_event (r:ℕ) (hr:3≤r) (p₀ γ ω K₀:ℝ)
    (hp₀:0<p₀) (hp₀1:p₀≤1) (hγ:0<γ) (hγ1:γ≤1) (hω:0<ω) (hK₀:1≤K₀):
    ∃ α₀:ℝ,0<α₀ ∧ α₀≤1 ∧ ∀ α L:ℝ,0<α → α≤α₀ → 0≤L →
    ∀ d q₀:ℕ,∀ hd:2≤d,∃ N:ℕ,
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
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
    1-1/(A.card:ℝ)^q₀≤
      (FiniteLaw.pi (rawWheelLaw (fun _=>pR) (fun _=>hpR) (fun _=>hpR1) d hd q hq hQ s hs hS)).probability
      (fun σ=>∀ (Q:SimpleGraph V) (H:V→U→Prop) (ℓ:ℝ),0≤ℓ →
        6*ℓ≤(p₀^6*γ/4)*A.card → 6*ℓ≤(p₀^6*γ/4)*U₀.card →
        (∀ v,((changed (A∩(rawWheelGraph P σ).neighborFinset v) (A∩Q.neighborFinset v)).card:ℝ)≤ℓ) →
        (∀ v,((changed (U₀∩Finset.univ.filter (rawWheelSpokes π d σ j v))
          (U₀∩Finset.univ.filter (H v))).card:ℝ)≤ℓ) →
        (∀ u∈U₀,((changed (A∩Finset.univ.filter (fun v=>rawWheelSpokes π d σ j v u))
          (A∩Finset.univ.filter (fun v=>H v u))).card:ℝ)≤ℓ) →
    ∀     (I X:Finset V) (J B:Finset U) (hIX:Disjoint I X) (hJB:Disjoint J B)
    (Nr Ns D₀:ℕ)
    (x y:Fin Nr→V) (hx:∀ i,x i∈I) (hy:∀ i,y i∈I)
    (hxy:∀ i,Q.Adj (x i) (y i)) (hFxy:∀ i,¬F.Adj (x i) (y i))
    (hedge:∀ i j,i≠j → ¬((x i=x j∧y i=y j)∨(x i=y j∧y i=x j)))
    (hend:∀ a,(Finset.univ.filter (fun i=>a=x i∨a=y i)).card≤D₀)
    (z:Fin Ns→V) (u:Fin Ns→U) (hz:∀ i,z i∈I) (hu:∀ i,u i∈J) (hH:∀ i,H (z i) (u i))
    (hspoke:Function.Injective (fun i=>(z i,u i)))
    (hsend:∀ a,(Finset.univ.filter (fun i=>a=z i)).card≤D₀)
    (hshub:∀ v,(Finset.univ.filter (fun i=>u i=v)).card≤D₀)
    (hJB0:J∪B⊆U₀)
    (hN:((Nr+Ns:ℕ):ℝ)≤α^2*(A.card:ℝ)^2) (hD:(D₀:ℝ)≤α*A.card)
    (hXA:((A\X).card:ℝ)≤p₀^6*γ*A.card/8)
    (hBU:((U₀\B).card:ℝ)≤p₀^6*γ*U₀.card/8)
,
    ∃ C:(Fin Nr⊕Fin Ns)→OrdinaryWheel Q F H r,
      (∀ i j,i≠j → Disjoint (ordinaryWheelResources (C i)) (ordinaryWheelResources (C j))) ∧
      (∀ i,ordinaryWheelResources (C i)∩ordinaryHostResources (spanningRestriction Q I)
        (fun a v=>H a v∧a∈I∧v∈J)=
        {Sum.elim (fun j=>Sum.inl s(x j,y j)) (fun j=>Sum.inr (z j,u j)) i}) ∧
      (∀ a,((wheelFamilyRim C).degree a:ℝ)≤12*α*A.card) ∧
      (∀ a,((Finset.univ.filter (fun v=>wheelFamilySpokes C a v)).card:ℝ)≤6*α*A.card) ∧
      (∀ v,((Finset.univ.filter (fun a=>wheelFamilySpokes C a v)).card:ℝ)≤3*α*A.card*r) ) :=by
  obtain ⟨α₀,hα₀,hα₀1,hpacking⟩:=prescribed_inner_packing_from_relative_counts r hr p₀ γ ω hp₀ hp₀1 hγ hγ1 hω
  refine ⟨α₀,hα₀,hα₀1,?_⟩
  intro α L hα hαsmall hL d q₀ hd
  obtain ⟨N₁,hN₁⟩:=hpacking α L hα hαsmall hL
  let ε₀:=p₀^6*γ/4
  have hε₀:0<ε₀:=by dsimp [ε₀];positivity
  obtain ⟨N₂,hN₂⟩:=ordinary_two_domain_neighbourhood_common_event K₀ ω (ε₀/2) hK₀ hω (by positivity) d q₀ hd
  refine ⟨max N₁ N₂,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P F π A U₀ hn hV hU hωU hFπ hF hdeg hnoshort
    pR pH hpR hpR1 hpR0 hpH0 q hq hQ s hs hS j hj
  have hh:=hN₂ V U Γ Color P F π A U₀ (by omega) hV hU hωU hFπ hnoshort
    pR hpR hpR1 q hq hQ s hs hS j pH hj
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ Q H ℓ hℓ hℓA hℓU hchangeQ hchangeHr hchangeHc
    I X J B hIX hJB Nr Ns D₀ x y hx hy hxy hFxy hedge hend z u hz hu hH hspoke hsend hshub
    hJB0 hN hD hXA hBU
  change 6*ℓ≤ε₀*A.card at hℓA
  change 6*ℓ≤ε₀*U₀.card at hℓU
  have hcounts:=ordinary_two_domain_counts_under_changes P (rawWheelGraph P σ) Q F
    (rawWheelSpokes π d σ j) H A U₀ pR pH (ε₀/2) ε₀ ℓ hℓ
    (by linarith only [hℓA]) (by linarith only [hℓU]) hchangeQ hchangeHr hchangeHc
    (by
      intro S J _hJB hSc hJc
      have ht:=(hσ.1 S J hSc (by omega)).le
      simpa only [hj,Finset.prod_const] using ht)
    (fun S hSc hI=>(hσ.2 S hSc hI).le)
  exact hN₁ V U P Q F H A I X U₀ J B hIX hJB Nr Ns D₀ x y hx hy hxy hFxy hedge hend
    z u hz hu hH hspoke hsend hshub hJB0 (by omega) hN hD hωU hF pR pH ε₀ hpR0 hpH0 le_rfl
    hdeg hXA hBU hcounts.1 (fun S hS hI=>hcounts.2 S (by omega) hI)

end Oberwolfach
