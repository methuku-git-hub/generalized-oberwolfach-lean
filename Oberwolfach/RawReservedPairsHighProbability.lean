module

public import Oberwolfach.RawIntervalAllPairCodegree
public import Oberwolfach.AsymptoticMargins

@[expose] public section
/-! The original reserved colour has uniform positive pair codegrees even
for overlapping interval windows. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_reserved_pair_high_probability
    (d:ℕ) (hd:2≤d) (s₀ δ:ℝ) (hs₀:0≤s₀) (hδ:0<δ):
    ∃N:ℕ,∀(V:Type) [Fintype V] [LinearOrder V],N≤Fintype.card V→
    ∀(U Γ Color:Type) [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color],
    0<Fintype.card U→Fintype.card U≤Fintype.card V→
    ∀(π:Equiv.Perm V) (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x) (j:Color) (hsl:∀u,s₀≤s u j),
    1-δ≤(FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
      (fun σ=>∀x y,x≠y→(5/8:ℝ)*s₀^2*Fintype.card U-(Fintype.card V:ℝ)^(3/4:ℝ)≤
        (((Finset.univ:Finset U).filter (fun u=>rawIntervalFamilyState π d σ (x,u)=some (Sum.inr j) ∧
          rawIntervalFamilyState π d σ (y,u)=some (Sum.inr j))).card:ℝ)):=by
  let c:ℝ:=1/(4*(d:ℝ)+3)^2
  have hc:0<c:=by dsimp [c];positivity
  obtain ⟨N₀,hN₀⟩:=eventually_stretchedExp_le_inv_pow 2 2 (c:=c) (p:=1/2) hc (by norm_num) 1
  obtain ⟨N₁,hN₁⟩:=exists_nat_gt (1/δ)
  refine ⟨max (max N₀ N₁) 1,?_⟩
  intro V _ _ hn U Γ Color _ _ _ _ hU0 hU π q hq hQ s hs hS hnoshort j hsl
  have hn0:0<Fintype.card V:=by omega
  have hnR:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn0
  have huR:(0:ℝ)<Fintype.card U:=by exact_mod_cast hU0
  have hUR:(Fintype.card U:ℝ)≤Fintype.card V:=by exact_mod_cast hU
  let t:ℝ:=(Fintype.card V:ℝ)^(3/4:ℝ)
  have ht:0<t:=by dsimp [t];positivity
  have hpow:t^2=(Fintype.card V:ℝ)^(1/2:ℝ)*(Fintype.card V:ℝ):=by
    dsimp [t]
    calc
      _ = (Fintype.card V:ℝ)^(3/2:ℝ):=by rw [←Real.rpow_natCast,←Real.rpow_mul hnR.le];norm_num
      _ = (Fintype.card V:ℝ)^(1/2:ℝ)*(Fintype.card V:ℝ)^(1:ℝ):=by rw [←Real.rpow_add hnR];norm_num
      _ = _:=by rw [Real.rpow_one]
  have harg:-2*t^2/((4*(d:ℝ)+3)^2*(2*(Fintype.card U:ℝ)))≤
      -c*(Fintype.card V:ℝ)^(1/2:ℝ):=by
    rw [hpow]
    dsimp [c]
    have hden:0<(4*(d:ℝ)+3)^2*(2*(Fintype.card U:ℝ)):=by positivity
    apply (div_le_iff₀ hden).2
    have hp:(0:ℝ)≤(Fintype.card V:ℝ)^(1/2:ℝ):=by positivity
    have heq:(1/(4*(d:ℝ)+3)^2)*(4*(d:ℝ)+3)^2=1:=by field_simp
    have hrw:-(1/(4*(d:ℝ)+3)^2)*(Fintype.card V:ℝ)^(1/2:ℝ)*
        ((4*(d:ℝ)+3)^2*(2*(Fintype.card U:ℝ)))=
        -2*(Fintype.card V:ℝ)^(1/2:ℝ)*(Fintype.card U:ℝ):=by
      have hh:(4*(d:ℝ)+3)^2≠0:=by positivity
      field_simp
    rw [hrw]
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hUR)]
  have hexp:=Real.exp_le_exp.mpr harg
  have hbudget:(Fintype.card V:ℝ)^2*(2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(2*(Fintype.card U:ℝ)))))≤
      2*(Fintype.card V:ℝ)^2*Real.exp (-c*(Fintype.card V:ℝ)^(1/2:ℝ)):=by
    have hh:=mul_le_mul_of_nonneg_left hexp (show 0≤2*(Fintype.card V:ℝ)^2 by positivity)
    nlinarith
  have hbound:=hN₀ (Fintype.card V) (by omega)
  have htwo:(Fintype.card V:ℝ)^(2:ℝ)=(Fintype.card V:ℝ)^2:=by simpa using (Real.rpow_natCast (Fintype.card V:ℝ) 2)
  rw [htwo] at hbound
  simp only [pow_one] at hbound
  have hsmall:1/(Fintype.card V:ℝ)≤δ:=by
    have hh:1/δ<(Fintype.card V:ℝ):=lt_of_lt_of_le hN₁ (by exact_mod_cast (show N₁≤Fintype.card V by omega))
    apply (div_le_iff₀ hnR).2
    have hh':1<(Fintype.card V:ℝ)*δ:=(div_lt_iff₀ hδ).1 hh
    linarith
  have hp:=raw_interval_all_pair_spoke_codegree_event π d hd q hq hQ s hs hS hnoshort hU0 j s₀ hs₀ hsl t ht
  have hfail:((Fintype.card V:ℝ)^2*(2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(2*(Fintype.card U:ℝ))))))≤δ:=
    hbudget.trans (hbound.trans hsmall)
  exact (sub_le_sub_left hfail 1).trans hp
end Oberwolfach
