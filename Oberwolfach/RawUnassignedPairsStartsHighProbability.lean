module

public import Oberwolfach.RawUnassignedPairCommonEvent
public import Oberwolfach.RawIntervalStartColumnsEvent
public import Oberwolfach.AsymptoticMargins
public import Oberwolfach.FiniteLawIntersectionLower

@[expose] public section
/-! Both pair availability and endpoint-start losses hold simultaneously
with arbitrarily high probability, uniformly over all original marginals. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_unassigned_pairs_and_starts_high_probability
    (d:ℕ) (hd:2≤d) (θ δ:ℝ) (hθ:0<θ) (hδ:0<δ) (hspace:1/(8*(d:ℝ))≤θ/2):
    ∃N:ℕ,∀(V:Type) [Fintype V] [LinearOrder V],N≤Fintype.card V→
    ∀(U Color:Type) [Fintype U] [DecidableEq U] [Fintype Color],
    0<Fintype.card U→Fintype.card U≤Fintype.card V→
    ∀(π:Equiv.Perm V) (q:U→Bool→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hrem:∀u,θ≤1-(∑g,q u g)-(∑j,s u j))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x),
    1-δ≤(FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
      (fun σ=>
        (∀x y,x≠y→(5/32:ℝ)*θ^2*Fintype.card U-(Fintype.card V:ℝ)^(3/4:ℝ)≤
          rawIntervalUnassignedPairColumnCount π d σ x y Finset.univ) ∧
        ∀v g,|rawIntervalStartColumnCount π d σ v g Finset.univ-∑u,q u g/(d:ℝ)|<(Fintype.card V:ℝ)^(3/4:ℝ)):=by
  obtain ⟨N₀,hN₀⟩:=eventually_stretchedExp_le_inv_pow 6 2 (c:=2) (p:=1/2) (by norm_num) (by norm_num) 1
  obtain ⟨N₁,hN₁⟩:=exists_nat_gt (1/δ)
  refine ⟨max (max N₀ N₁) 1,?_⟩
  intro V _ _ hn U Color _ _ _ hU0 hU π q hq hQ s hs hS hrem hnoshort
  let n:ℝ:=Fintype.card V
  let u:ℝ:=Fintype.card U
  let t:ℝ:=n^(3/4:ℝ)
  have hn0:0<n:=by dsimp [n];exact_mod_cast (show 0<Fintype.card V by omega)
  have hu0:0<u:=by dsimp [u];exact_mod_cast hU0
  have hun:u≤n:=by dsimp [u,n];exact_mod_cast hU
  have hn1:1≤n:=by dsimp [n];exact_mod_cast (show 1≤Fintype.card V by omega)
  have ht:0<t:=by dsimp [t];positivity
  have hpow:t^2=n^(1/2:ℝ)*n:=by
    dsimp [t]
    calc
      _ = n^(3/2:ℝ):=by rw [←Real.rpow_natCast,←Real.rpow_mul hn0.le];norm_num
      _ = n^(1/2:ℝ)*n^(1:ℝ):=by rw [←Real.rpow_add hn0];norm_num
      _ = _:=by rw [Real.rpow_one]
  have harg:-2*t^2/u≤-2*n^(1/2:ℝ):=by
    rw [hpow]
    have hp:(0:ℝ)≤n^(1/2:ℝ):=by positivity
    apply (div_le_iff₀ hu0).2
    nlinarith
  have hexp:=Real.exp_le_exp.mpr harg
  have hcoeff:2*n^2+4*n≤6*n^2:=by nlinarith
  have hbudget:2*n^2*Real.exp (-2*t^2/u)+4*n*Real.exp (-2*t^2/u)≤
      6*n^2*Real.exp (-2*n^(1/2:ℝ)):=by
    have hc0:0≤2*n^2+4*n:=by positivity
    have he0:0≤Real.exp (-2*n^(1/2:ℝ)):=by positivity
    nlinarith [mul_le_mul_of_nonneg_left hexp hc0,mul_le_mul_of_nonneg_right hcoeff he0]
  have hbound:=hN₀ (Fintype.card V) (by omega)
  have htwo:(Fintype.card V:ℝ)^(2:ℝ)=(Fintype.card V:ℝ)^2:=by simpa using (Real.rpow_natCast (Fintype.card V:ℝ) 2)
  rw [htwo] at hbound
  simp only [pow_one] at hbound
  have hsmall:1/n≤δ:=by
    have hh:1/δ<n:=lt_of_lt_of_le hN₁ (by dsimp [n];exact_mod_cast (show N₁≤Fintype.card V by omega))
    apply (div_le_iff₀ hn0).2
    have hh':1<n*δ:=(div_lt_iff₀ hδ).1 hh
    linarith
  let μ:=FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
  let A:=fun (σ:RawIntervalFamilyOutcome V U Bool Color)=>∀x y,x≠y→(5/32:ℝ)*θ^2*Fintype.card U-t≤rawIntervalUnassignedPairColumnCount π d σ x y Finset.univ
  let B:=fun (σ:RawIntervalFamilyOutcome V U Bool Color)=>∀v g,|rawIntervalStartColumnCount π d σ v g Finset.univ-∑u,q u g/(d:ℝ)|<t
  have hA:1-2*n^2*Real.exp (-2*t^2/u)≤μ.probability A:=
    raw_unassigned_pairs_common_event π d hd q hq hQ s hs hS θ hθ hrem hspace hnoshort t ht.le
  have hB:1-4*n*Real.exp (-2*t^2/u)≤μ.probability B:=by
    have hh:=raw_interval_start_columns_event π d hd q hq hQ s hs hS hnoshort t ht.le
    simp only [Fintype.card_bool,Nat.cast_ofNat] at hh
    dsimp [n,u,μ,B]
    nlinarith [hh]
  have hboth:=finiteLaw_intersection_lower μ A B (2*n^2*Real.exp (-2*t^2/u)) (4*n*Real.exp (-2*t^2/u)) hA hB
  have hfail:2*n^2*Real.exp (-2*t^2/u)+4*n*Real.exp (-2*t^2/u)≤δ:=by
    apply hbudget.trans
    dsimp [n]
    exact hbound.trans (by simpa [n] using hsmall)
  change 1-δ≤μ.probability (fun σ=>A σ ∧ B σ)
  linarith
end Oberwolfach
