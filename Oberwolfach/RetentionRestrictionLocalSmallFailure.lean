module

public import Oberwolfach.RetentionRestrictionLocalFamily
public import Oberwolfach.RetentionLocalBinomialTail
public import Oberwolfach.RetentionLocalFamilyErrorBudget

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem retained_restriction_local_family_small_failure
    (d:ℕ) (ζ K b c δ:ℝ) (hζ:0<ζ) (hK:0≤K) (hb:0<b) (hc:0<c) (hδ:0<δ):
    ∃m:ℕ,1≤m ∧ ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    ∀(I:Type) (T:Finset I) (A:I→Finset V) (H:I→Finset U) (n:ℕ),
    (∀i∈T,m≤(A i).card) → Set.InjOn (fun i=>(A i).card) T →
    (∀i∈T,(H i).card≤(A i).card) → (∀i∈T,c*((A i).card:ℝ)≤(H i).card) →
    (∀i∈T,(A i).card≤n) →
    ∀(π:Equiv.Perm V), (∀i∈T,∀x,π x∈A i↔x∈A i) →
    ∀(σ:RawIntervalFamilyOutcome V U Γ Color) (g₀:Γ) (t:ℕ)
    (ht:∀a,t≤(rawStartHubSet π d σ g₀ a).card) (p:ℝ) (hp:0≤p)
    (hpn:p≤K*(n:ℝ)^(-b))
    (hrate:∀a,(((rawStartHubSet π d σ g₀ a).card-t:ℕ):ℝ)/(rawStartHubSet π d σ g₀ a).card≤p),
    let μ:=startRetentionLaw (rawStartHubSet π d σ g₀) t ht
    1-δ≤μ.probability (fun J=>∀i∈T,RetainedRestrictionLocalGood π d σ g₀ t (A i) (H i) ζ J):=by
  let a:ℝ:=ζ/(d+1:ℕ)
  have ha:0<a:=by dsimp [a];positivity
  obtain ⟨N,hN,hTail⟩:=retention_binomial_tail_at_local_scale K a b hK ha hb 6
  obtain ⟨M,hM,hBudget⟩:=retention_local_family_error_budget d c δ hc hδ
  obtain ⟨m₀,hm₀⟩:=exists_nat_gt ((N:ℝ)/c)
  let m:=max (max N M) m₀
  have hmN:N≤m:=le_trans (le_max_left N M) (le_max_left _ _)
  have hmM:M≤m:=le_trans (le_max_right N M) (le_max_left _ _)
  have hm0:m₀≤m:=le_max_right _ _
  refine ⟨m,le_trans hN hmN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ I T A H n hmin hinj hHup hHlo hAn π hInv σ g₀ t ht p hp hpn hrate μ
  have hHmin:∀i∈T,N≤(H i).card:=by
    intro i hi
    have hmR:(m₀:ℝ)≤(A i).card:=by exact_mod_cast (le_trans hm0 (hmin i hi))
    have hh:(N:ℝ)<(m₀:ℝ)*c:=(div_lt_iff₀ hc).1 hm₀
    have hmR':(m₀:ℝ)*c≤(A i).card*c:=mul_le_mul_of_nonneg_right hmR hc.le
    have hle:(N:ℝ)≤(H i).card:=by nlinarith only [hh,hmR',hHlo i hi]
    exact_mod_cast hle
  have hAmin:∀i∈T,N≤(A i).card:=by intro i hi;exact le_trans hmN (hmin i hi)
  have hHn:∀i∈T,(H i).card≤n:=by intro i hi;exact le_trans (hHup i hi) (hAn i hi)
  let Fr:=fun i:I=>1/((A i).card:ℝ)^6
  let Fc:=fun i:I=>1/((H i).card:ℝ)^6
  have hrow:∀i∈T,((A i).card.choose (Nat.ceil (ζ*(A i).card/(d+1:ℕ))):ℝ)*p^(Nat.ceil (ζ*(A i).card/(d+1:ℕ)))≤Fr i:=by
    intro i hi
    have hh:=hTail (A i).card n (hAmin i hi) (hAn i hi) p hp hpn
    have he:a*((A i).card:ℝ)=ζ*(A i).card/(d+1:ℕ):=by dsimp [a];ring
    simpa only [he,Fr] using hh
  have hcol:∀i∈T,((H i).card.choose (Nat.ceil (ζ*(H i).card/(d+1:ℕ))):ℝ)*p^(Nat.ceil (ζ*(H i).card/(d+1:ℕ)))≤Fc i:=by
    intro i hi
    have hh:=hTail (H i).card n (hHmin i hi) (hHn i hi) p hp hpn
    have he:a*((H i).card:ℝ)=ζ*(H i).card/(d+1:ℕ):=by dsimp [a];ring
    simpa only [he,Fc] using hh
  have herror:(∑i∈T,(((H i).card:ℝ)*Fr i+((A i).card:ℝ)*((d+1:ℕ)*Fc i)))≤δ:=by
    apply hBudget I T (fun i=>(A i).card) (fun i=>(H i).card)
    · intro i hi;exact le_trans hmM (hmin i hi)
    · exact hinj
    · intro i hi;exact_mod_cast hHup i hi
    · exact hHlo
  have hh:=retained_restriction_local_family π d σ g₀ t ht I T A H hInv ζ p Fr Fc hζ.le hp hrate hrow hcol
  dsimp only at hh
  linarith only [hh,herror]
end Oberwolfach
