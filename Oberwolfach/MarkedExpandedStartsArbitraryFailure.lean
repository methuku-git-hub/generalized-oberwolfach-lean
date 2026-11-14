module

public import Oberwolfach.MarkedExpandedStartCounts
public import Oberwolfach.OrientationMargins

@[expose] public section
/-! Uniform high-probability start counts for at most two interval colours,
with a positive hub set no larger than the vertex set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_expanded_starts_arbitrary_failure (δ:ℝ) (hδ:0<δ) :
    ∃ N:ℕ,∀ (V:Type) [Fintype V] [LinearOrder V],N≤Fintype.card V→
    ∀ (U Γ Color:Type) [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq U],
    0<Fintype.card U→Fintype.card U≤Fintype.card V→Fintype.card Γ≤2→
    ∀ (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a)),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    1-δ≤(μ.sigma (fun ω=>ν (f ω))).probability
      (fun z=>∀ g a,|((rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g a).card:ℝ)-(∑ u,q u g/(d:ℝ))|<(Fintype.card V:ℝ)^(3/5:ℝ)) := by
  obtain ⟨N,hN⟩:=eventually_stretchedExp_le_inv_pow (4:ℝ) 1
    (c:=2) (p:=1/5) (by norm_num) (by norm_num) 1
  obtain ⟨Nδ,hNδ⟩:=exists_nat_gt (1/δ)
  refine ⟨max (max N Nδ) 1,?_⟩
  intro V _ _ hn U Γ Color _ _ _ _ hm hmn hΓ π d hd p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort F _ ν
  have hnpos:(0:ℝ)<Fintype.card V:=by exact_mod_cast (show 0<Fintype.card V by omega)
  have hmpos:(0:ℝ)<Fintype.card U:=by exact_mod_cast hm
  have hmnR:(Fintype.card U:ℝ)≤Fintype.card V:=by exact_mod_cast hmn
  have hΓR:(Fintype.card Γ:ℝ)≤2:=by exact_mod_cast hΓ
  have hb:=hN (Fintype.card V) (by omega)
  simp only [Real.rpow_one,pow_one] at hb
  have ht:0<(Fintype.card V:ℝ)^(3/5:ℝ):=by positivity
  have hh:=raw_expanded_marked_all_colours_starts_event π d hd p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort F ν _ ht
  have hdiv:2*((Fintype.card V:ℝ)^(3/5:ℝ))^2/(Fintype.card V:ℝ)≤
      2*((Fintype.card V:ℝ)^(3/5:ℝ))^2/(Fintype.card U:ℝ):=
    div_le_div_of_nonneg_left (by positivity) hmpos hmnR
  have harg:-2*((Fintype.card V:ℝ)^(3/5:ℝ))^2/(Fintype.card U:ℝ)≤
      -2*((Fintype.card V:ℝ)^(3/5:ℝ))^2/(Fintype.card V:ℝ):=by
    convert neg_le_neg hdiv using 1 <;> ring
  rw [threeFifths_tail_exponent hnpos] at harg
  have hexp:=Real.exp_le_exp.mpr harg
  have hcoeff:(2:ℝ)*Fintype.card Γ*Fintype.card V≤4*Fintype.card V:=by nlinarith
  have hbudget:2*(Fintype.card Γ:ℝ)*Fintype.card V*Real.exp (-2*((Fintype.card V:ℝ)^(3/5:ℝ))^2/Fintype.card U)≤
      4*(Fintype.card V:ℝ)*Real.exp (-2*(Fintype.card V:ℝ)^(1/5:ℝ)):=by
    exact (mul_le_mul_of_nonneg_left hexp (by positivity)).trans (mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le)
  have hnδ:(1/δ:ℝ)<Fintype.card V:=lt_of_lt_of_le hNδ (by exact_mod_cast (show Nδ≤Fintype.card V by omega))
  have hprod:(1:ℝ)≤δ*Fintype.card V:=by
    have hh:1<(Fintype.card V:ℝ)*δ:=(div_lt_iff₀ hδ).mp hnδ
    nlinarith
  have hsmall:(1:ℝ)/(Fintype.card V:ℝ)≤δ:=(div_le_iff₀ hnpos).2 (by nlinarith)
  have hnum:1-δ≤1-2*(Fintype.card Γ:ℝ)*Fintype.card V*Real.exp (-2*((Fintype.card V:ℝ)^(3/5:ℝ))^2/Fintype.card U):=by
    exact sub_le_sub_left (hbudget.trans (hb.trans hsmall)) 1
  exact hnum.trans hh
end Oberwolfach
