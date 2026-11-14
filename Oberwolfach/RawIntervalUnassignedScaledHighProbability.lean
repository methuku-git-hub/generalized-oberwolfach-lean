module

public import Oberwolfach.RawIntervalUnassignedHighProbability
public import Oberwolfach.RawIntervalUnassignedCountsEvent
public import Oberwolfach.OrientationMargins

@[expose] public section
/-! High probability for fixed domains, at the n^(3/4) scale. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_expanded_unassigned_fixed_domains_scaled_high_probability (d:ℕ) (hd:2≤d) (a failure:ℝ) (ha:0<a) (hfailure:0<failure):
    ∃ N:ℕ,∀ (V:Type) [Fintype V] [LinearOrder V],N≤Fintype.card V→
    ∀ (U Γ Color:Type) [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq U],
    Fintype.card U≤Fintype.card V→
    ∀ (π:Equiv.Perm V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a))
    (A:Finset V) (J:Finset U),J.Nonempty→
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    1-failure≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>
      (∀ u,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) u A-(A.card:ℝ)*(1-(∑ g,q u g)-(∑ j,s u j))|<a*(Fintype.card V:ℝ)^(3/4:ℝ)) ∧
      (∀ v,|rawIntervalUnassignedColumnCount π d (fun e=>z.1 (Sum.inr e)) v J-∑ u∈J,(1-(∑ g,q u g)-(∑ j,s u j))|<a*(Fintype.card V:ℝ)^(3/4:ℝ))) := by
  have hd0:(0:ℝ)≤d:=by positivity
  let c:ℝ:=2*a^2/((4*(d:ℝ)+3)^2)
  have hc:0<c:=by dsimp [c];positivity
  have hc2:c≤2*a^2:=by
    dsimp [c]
    apply (div_le_iff₀ (by positivity)).2
    have hdensq:(1:ℝ)≤(4*(d:ℝ)+3)^2:=by nlinarith
    have hprod:=mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hdensq)
    nlinarith
  obtain ⟨N,hN⟩:=eventually_stretchedExp_le_inv_pow (4:ℝ) 1 (c:=c) (p:=1/2) hc (by norm_num) 1
  obtain ⟨M,hM⟩:=exists_nat_gt (1/failure)
  refine ⟨max N (max M 1),?_⟩
  intro V _ _ hn U Γ Color _ _ _ _ hmn π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort F _ ν A J hJ
  have hnM:M≤Fintype.card V:=by omega
  have hnN:0<Fintype.card V:=by omega
  have hnpos:(0:ℝ)<Fintype.card V:=by exact_mod_cast hnN
  have hJpos:(0:ℝ)<J.card:=by exact_mod_cast hJ.card_pos
  have hmnR:(Fintype.card U:ℝ)≤Fintype.card V:=by exact_mod_cast hmn
  have hJn:(J.card:ℝ)≤Fintype.card V:=by exact_mod_cast ((Finset.card_le_univ J).trans hmn)
  have hb:=hN (Fintype.card V) (le_trans (le_max_left _ _) hn)
  simp only [Real.rpow_one,pow_one] at hb
  have ht:0<a*(Fintype.card V:ℝ)^(3/4:ℝ):=by positivity
  have hh:=raw_expanded_unassigned_fixed_domains_event π d hd p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnN hnoshort F ν A J _ ht
  have heq:(a*(Fintype.card V:ℝ)^(3/4:ℝ))^2=a^2*((Fintype.card V:ℝ)^(1/2:ℝ)*(Fintype.card V:ℝ)):=by
    have hbase:((Fintype.card V:ℝ)^(3/4:ℝ))^2=(Fintype.card V:ℝ)^(1/2:ℝ)*(Fintype.card V:ℝ):=by
      calc
        _ = (Fintype.card V:ℝ)^(3/2:ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le];norm_num
        _ = (Fintype.card V:ℝ)^(1/2:ℝ)*(Fintype.card V:ℝ)^(1:ℝ) := by rw [← Real.rpow_add hnpos];norm_num
        _ = _ := by rw [Real.rpow_one]
    nlinarith [sq_nonneg a]
  have harg: -2*(a*(Fintype.card V:ℝ)^(3/4:ℝ))^2/((4*(d:ℝ)+3)^2*(Fintype.card V:ℝ)) =
      -c*(Fintype.card V:ℝ)^(1/2:ℝ):=by rw [heq];dsimp [c];field_simp
  rw [harg] at hh
  have hdiv:2*(a*(Fintype.card V:ℝ)^(3/4:ℝ))^2/(Fintype.card V:ℝ)≤
      2*(a*(Fintype.card V:ℝ)^(3/4:ℝ))^2/J.card:=div_le_div_of_nonneg_left (by positivity) hJpos hJn
  have harg2:-2*(a*(Fintype.card V:ℝ)^(3/4:ℝ))^2/J.card≤
      -2*(a*(Fintype.card V:ℝ)^(3/4:ℝ))^2/(Fintype.card V:ℝ):=by convert neg_le_neg hdiv using 1 <;> ring
  have heq2:-2*(a*(Fintype.card V:ℝ)^(3/4:ℝ))^2/(Fintype.card V:ℝ) = -2*a^2*(Fintype.card V:ℝ)^(1/2:ℝ):=by rw [heq];field_simp
  rw [heq2] at harg2
  have harg3:-2*(a*(Fintype.card V:ℝ)^(3/4:ℝ))^2/J.card≤ -c*(Fintype.card V:ℝ)^(1/2:ℝ):=by
    have hh':=mul_le_mul_of_nonneg_right hc2 (show 0≤(Fintype.card V:ℝ)^(1/2:ℝ) by positivity)
    linarith
  have hexp:=Real.exp_le_exp.mpr harg3
  have hbudget:2*(Fintype.card U:ℝ)*Real.exp (-c*(Fintype.card V:ℝ)^(1/2:ℝ))+
      2*(Fintype.card V:ℝ)*Real.exp (-2*(a*(Fintype.card V:ℝ)^(3/4:ℝ))^2/J.card)≤
      4*(Fintype.card V:ℝ)*Real.exp (-c*(Fintype.card V:ℝ)^(1/2:ℝ)):=by
    have h1:=mul_le_mul_of_nonneg_right (show 2*(Fintype.card U:ℝ)≤2*Fintype.card V by linarith) (Real.exp_pos (-c*(Fintype.card V:ℝ)^(1/2:ℝ))).le
    have h2:=mul_le_mul_of_nonneg_left hexp (show 0≤2*(Fintype.card V:ℝ) by positivity)
    linarith
  have hsmall:(1:ℝ)/(Fintype.card V:ℝ)≤failure:=by
    have hMreal:(M:ℝ)≤Fintype.card V:=by exact_mod_cast hnM
    have hbnd:1/failure≤(Fintype.card V:ℝ):=hM.le.trans hMreal
    have hmul:1≤(Fintype.card V:ℝ)*failure:=(div_le_iff₀ hfailure).mp hbnd
    exact (div_le_iff₀ hnpos).mpr (by nlinarith)
  have hnum:1-failure≤1-2*(Fintype.card U:ℝ)*Real.exp (-c*(Fintype.card V:ℝ)^(1/2:ℝ))-
      2*(Fintype.card V:ℝ)*Real.exp (-2*(a*(Fintype.card V:ℝ)^(3/4:ℝ))^2/J.card):=by
    have h:=sub_le_sub_left (hbudget.trans (hb.trans hsmall)) 1
    linarith
  exact hnum.trans hh
end Oberwolfach
