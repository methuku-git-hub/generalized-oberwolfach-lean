module

public import Oberwolfach.RawAbsorberColumnLocalEvent
public import Oberwolfach.FiniteHighEventsCommon

@[expose] public section
/-! Local unassigned-spoke columns over a family of vertex and hub sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_interval_absorber_column_local_family_event
    {V U Color:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype Color]
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (q:U→Bool→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (I:Type) (T:Finset I) (A:I→Finset V) (J:I→Finset U) (t:I→ℝ)
    (hJ:∀i∈T,0<(J i).card) (hJA:∀i∈T,(J i).card≤(A i).card) (ht:∀i∈T,0<t i):
    let μ:=FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
    1-∑i∈T,8*((A i).card:ℝ)*Real.exp (-2*(t i)^2/((A i).card:ℝ))≤
      μ.probability (fun σ=>∀i∈T,∀v∈A i,∀g, |rawIntervalAssignedLabelColumnCount π d σ v g (J i)-∑u∈J i,q u g|<t i ∧
        |rawIntervalStartColumnCount π d σ ((π^d).symm v) g (J i)-∑u∈J i,q u g/(d:ℝ)|<t i):=by
  intro μ
  let E:=fun i (σ:RawIntervalFamilyOutcome V U Bool Color)=>∀v∈A i,∀g, |rawIntervalAssignedLabelColumnCount π d σ v g (J i)-∑u∈J i,q u g|<t i ∧
    |rawIntervalStartColumnCount π d σ ((π^d).symm v) g (J i)-∑u∈J i,q u g/(d:ℝ)|<t i
  have hEach:∀i∈T,1-8*((A i).card:ℝ)*Real.exp (-2*(t i)^2/((A i).card:ℝ))≤μ.probability (E i):=by
    intro i hi
    have hj:(0:ℝ)<(J i).card:=by exact_mod_cast hJ i hi
    have ha:(0:ℝ)<(A i).card:=lt_of_lt_of_le hj (by exact_mod_cast hJA i hi)
    have hja:((J i).card:ℝ)≤(A i).card:=by exact_mod_cast hJA i hi
    have hinv:1/((A i).card:ℝ)≤1/((J i).card:ℝ):=one_div_le_one_div_of_le hj hja
    have harg:-2*(t i)^2/((J i).card:ℝ)≤-2*(t i)^2/((A i).card:ℝ):=by
      have hmul:=mul_le_mul_of_nonneg_left hinv (show (0:ℝ)≤2*(t i)^2 by positivity)
      simp only [div_eq_mul_inv, one_mul] at hmul ⊢
      nlinarith only [hmul]
    have hexp:=Real.exp_le_exp.mpr harg
    have hfactor:=mul_le_mul_of_nonneg_left hexp (show (0:ℝ)≤8*((A i).card:ℝ) by positivity)
    have hh:=raw_interval_absorber_column_local_event π d hd q hq hQ s hs hS hnoshort (A i) (J i) (t i) (ht i hi)
    linarith only [hh,hfactor]
  exact finiteLaw_high_events_common μ T E
    (fun i=>8*((A i).card:ℝ)*Real.exp (-2*(t i)^2/((A i).card:ℝ))) hEach
end Oberwolfach
