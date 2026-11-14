module

public import Oberwolfach.RawIntervalHubStartHighProbability

@[expose] public section
/-! Inverse-order failure probability for the same fixed-domain event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_expanded_hub_starts_highProbability_invCard (d:ℕ) (hd:2≤d):
    ∃ N:ℕ,∀ (V:Type) [Fintype V] [LinearOrder V],N≤Fintype.card V→
    ∀ (U Γ Color:Type) [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq U],
    Fintype.card U≤Fintype.card V→Fintype.card Γ≤2→
    ∀ (π:Equiv.Perm V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a)),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    1-1/(Fintype.card V:ℝ)≤(μ.sigma (fun ω=>ν (f ω))).probability
      (fun z=>∀ u g,|rawIntervalHubStartCount π d g (fun e=>z.1 (Sum.inr e)) u-(Fintype.card V:ℝ)*q u g/d|<
        (Fintype.card V:ℝ)^(3/4:ℝ)/d) := by
  have hdpos:(0:ℝ)<d:=by exact_mod_cast (show 0<d by omega)
  let c:ℝ:=2/((4*(d:ℝ)+3)^2*(d:ℝ)^2)
  have hc:0<c:=by dsimp [c];positivity
  obtain ⟨N,hN⟩:=eventually_stretchedExp_le_inv_pow (4:ℝ) 1
    (c:=c) (p:=1/2) hc (by norm_num) 1
  refine ⟨max N 1000,?_⟩
  intro V _ _ hn U Γ Color _ _ _ _ hmn hΓ π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort F _ ν
  have hn1000:1000≤Fintype.card V:=le_trans (le_max_right _ _) hn
  have hnN:0<Fintype.card V:=by omega
  have hnpos:(0:ℝ)<Fintype.card V:=by exact_mod_cast hnN
  have hmnR:(Fintype.card U:ℝ)≤Fintype.card V:=by exact_mod_cast hmn
  have hΓR:(Fintype.card Γ:ℝ)≤2:=by exact_mod_cast hΓ
  have hb:=hN (Fintype.card V) (le_trans (le_max_left _ _) hn)
  simp only [Real.rpow_one,pow_one] at hb
  have ht:0<(Fintype.card V:ℝ)^(3/4:ℝ)/d:=by positivity
  have hh:=raw_expanded_marked_hub_starts_all_event π d hd p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnN hnoshort F ν _ ht
  have heq:((Fintype.card V:ℝ)^(3/4:ℝ))^2=(Fintype.card V:ℝ)^(1/2:ℝ)*(Fintype.card V:ℝ):=by
    calc
      _ = (Fintype.card V:ℝ)^(3/2:ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le];norm_num
      _ = (Fintype.card V:ℝ)^(1/2:ℝ)*(Fintype.card V:ℝ)^(1:ℝ) := by
        rw [← Real.rpow_add hnpos];norm_num
      _ = _ := by rw [Real.rpow_one]
  have harg: -2*((Fintype.card V:ℝ)^(3/4:ℝ)/d)^2/((4*(d:ℝ)+3)^2*(Fintype.card V:ℝ)) =
      -c*(Fintype.card V:ℝ)^(1/2:ℝ):=by
    rw [div_pow,heq]
    dsimp [c]
    field_simp
  rw [harg] at hh
  have hcoeff:(2:ℝ)*Fintype.card U*Fintype.card Γ≤4*Fintype.card V:=by
    nlinarith [mul_nonneg (show 0≤(Fintype.card U:ℝ) by positivity) (show 2-(Fintype.card Γ:ℝ)≥0 by linarith)]
  have hbudget:2*(Fintype.card U:ℝ)*Fintype.card Γ*Real.exp (-c*(Fintype.card V:ℝ)^(1/2:ℝ))≤
      4*(Fintype.card V:ℝ)*Real.exp (-c*(Fintype.card V:ℝ)^(1/2:ℝ)):=
    mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le
  have hsmall:(1:ℝ)/(Fintype.card V:ℝ)≤1/1000:=by
    apply (div_le_iff₀ hnpos).2
    have : (1000:ℝ)≤Fintype.card V:=by exact_mod_cast hn1000
    linarith
  have hnum:1-1/(Fintype.card V:ℝ)≤1-2*(Fintype.card U:ℝ)*Fintype.card Γ*Real.exp (-c*(Fintype.card V:ℝ)^(1/2:ℝ)):=by
    convert sub_le_sub_left (hbudget.trans hb) 1 using 1 <;> norm_num
  exact hnum.trans hh
end Oberwolfach
