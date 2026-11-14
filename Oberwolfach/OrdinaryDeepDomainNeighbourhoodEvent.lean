module

public import Oberwolfach.RawOrdinaryRowEvent
public import Oberwolfach.RawOrdinaryDomainIndexEvent
public import Oberwolfach.ConfigurationFailureMargins
public import Oberwolfach.GoodPlacementEvents

@[expose] public section

/-! A polynomially high-probability event for all ordinary row and index
counts on fixed domains under the supplied original sampling law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_three_domain_neighbourhood_common_event (K ω ε:ℝ) (hK:1≤K) (hω:0<ω) (hε:0<ε)
    (d q₀:ℕ) (hd:2≤d):
    ∃ N:ℕ,∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    ∀ (P F:SimpleGraph V) (π:Equiv.Perm V) (A:Finset V) (B:Finset U),N≤A.card →
      (Fintype.card V:ℝ)≤K*A.card → (Fintype.card U:ℝ)≤K*A.card → ω*A.card≤(B.card:ℝ) →
      permutationConflictGraph π (3*d)≤F →
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ (p:ℝ) (hp:0≤p) (hp1:p≤1)
      (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (j:Color) (pH:ℝ),(∀ u,s u j=pH) →
    1-1/(A.card:ℝ)^q₀≤
      (FiniteLaw.pi (rawWheelLaw (fun _=>p) (fun _=>hp) (fun _=>hp1) d hd q hq hQ s hs hS)).probability
        (fun σ=>RawOrdinaryRows P π d 3 A p s j (ε*A.card) σ ∧
          RawOrdinaryDomainIndices F π d 3 B pH j (ε*B.card) σ):=by
  have hK0:0<K:=lt_of_lt_of_le zero_lt_one hK
  obtain ⟨N₁,h₁⟩:=linear_deviation_failure_eventually_small ((K+1)^6) ((4*(d:ℝ)+3)^2*14) ε
    (by positivity) hε 6 (q₀+1)
  obtain ⟨N₂,h₂⟩:=linear_deviation_failure_eventually_small ((K+1)^3) ((4*(d:ℝ)+3)^2*4*K) (ε*ω)
    (by positivity) (mul_pos hε hω) 3 (q₀+1)
  refine ⟨max 2 (max N₁ N₂),?_⟩
  intro V U Γ Color _ _ _ _ _ _ P F π A B hn hV hU hωU hF hnoshort p hp hp1 q hq hQ s hs hS j pH hj
  have ha:0<A.card:=by omega
  have ha0:(0:ℝ)<A.card:=Nat.cast_pos.mpr ha
  have ha1:(1:ℝ)≤A.card:=by exact_mod_cast ha
  have hm0:(0:ℝ)<B.card:=(mul_pos hω ha0).trans_le hωU
  have hm:0<B.card:=Nat.cast_pos.mp hm0
  have hBup:(B.card:ℝ)≤K*A.card:=(Nat.cast_le.mpr (Finset.card_le_univ B)).trans hU
  have hV':(Fintype.card V:ℝ)+1≤(K+1)*A.card:=by nlinarith only [hV,ha1]
  have hU':(Fintype.card U:ℝ)+1≤(K+1)*A.card:=by nlinarith only [hU,ha1]
  have hc₁:(Fintype.card V+1:ℝ)^3*(Fintype.card U+1:ℝ)^3≤(K+1)^6*(A.card:ℝ)^6:=by
    calc
      _≤((K+1)*A.card)^3*((K+1)*A.card)^3:=by gcongr
      _=_:=by ring
  have hc₂:(Fintype.card V+1:ℝ)^3≤(K+1)^3*(A.card:ℝ)^3:=by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) hV' 3
  have ht₁:=h₁ A.card (by omega) _ ((4*(d:ℝ)+3)^2*(14*A.card)) (by positivity) hc₁
    (by positivity) (by ring_nf;exact le_rfl)
  have ht₂:=h₂ A.card (by omega) _ ((4*(d:ℝ)+3)^2*(4*B.card)) (by positivity) hc₂
    (by positivity) (by nlinarith only [mul_le_mul_of_nonneg_left hBup (show 0≤(4*(d:ℝ)+3)^2*4 by positivity)])
  let μ:=FiniteLaw.pi (rawWheelLaw (fun _:Sym2 V=>p) (fun _=>hp) (fun _=>hp1) d hd q hq hQ s hs hS)
  have hr:1-1/(A.card:ℝ)^(q₀+1)≤μ.probability (RawOrdinaryRows P π d 3 A p s j (ε*A.card)):=by
    have hh:=rawOrdinaryRows_common_event P π d hd p hp hp1 q hq hQ s hs hS hnoshort
      A (Finset.card_pos.mp ha) 3 j (ε*A.card) (by positivity)
    norm_num only [Nat.cast_ofNat] at hh
    exact (sub_le_sub_left ht₁ 1).trans hh
  have hi:1-1/(A.card:ℝ)^(q₀+1)≤μ.probability (RawOrdinaryDomainIndices F π d 3 B pH j (ε*B.card)):=by
    have hh:=rawOrdinaryDomainIndices_common_event F π (fun _=>p) (fun _=>hp) (fun _=>hp1)
      d hd q hq hQ s hs hS hnoshort hF B hm 3 j pH hj ((ε*ω)*A.card) (by positivity)
    norm_num only [Nat.cast_ofNat] at hh
    apply ((sub_le_sub_left ht₂ 1).trans hh).trans
    apply finiteLaw_probability_mono
    intro σ hσ S hSc hSI
    have ht:=hσ S hSc hSI
    exact ht.trans_le (by nlinarith only [mul_le_mul_of_nonneg_left hωU hε.le])
  have hh:=finiteLaw_good_intersection μ
    (RawOrdinaryRows P π d 3 A p s j (ε*A.card))
    (RawOrdinaryDomainIndices F π d 3 B pH j (ε*B.card)) (1/(A.card:ℝ)^(q₀+1)) hi
  have hnum:=scaled_inverse_power_le A.card q₀ ha 2 (by exact_mod_cast (show 2≤A.card by omega))
  change 1-1/(A.card:ℝ)^q₀≤μ.probability _
  have hnum':2*(1/(A.card:ℝ)^(q₀+1))≤1/(A.card:ℝ)^q₀:=by
    convert hnum using 1 <;> ring
  linarith only [hh,hr,hnum']

end Oberwolfach
