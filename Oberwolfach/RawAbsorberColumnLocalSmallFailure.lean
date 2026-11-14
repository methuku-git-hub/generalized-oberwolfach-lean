module

public import Oberwolfach.RawAbsorberColumnLocalFamily
public import Oberwolfach.LocalRowFamilyErrorBudget
public import Oberwolfach.RawUnassignedHubLocalFamily
public import Oberwolfach.LocalRowFamilyGeneralErrorBudget

@[expose] public section
/-! Distinct local scales have a uniform unassigned-spoke failure budget. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_interval_absorber_column_local_family_small_failure
    (d:ℕ) (hd:2≤d) (δ:ℝ) (hδ:0<δ) :
    ∃m:ℕ,1≤m ∧ ∀(V U Color:Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
      [Fintype Color],
    ∀(I:Type) (T:Finset I) (A:I→Finset V) (J:I→Finset U),
    (∀i∈T,m≤(A i).card) → Set.InjOn (fun i=>(A i).card) T →
    (∀i∈T,0<(J i).card) → (∀i∈T,(J i).card≤(A i).card) →
    ∀(π:Equiv.Perm V) (q:U→Bool→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x),
    let μ:=FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
    1-δ≤μ.probability (fun σ=>∀i∈T,∀v∈A i,∀g, |rawIntervalAssignedLabelColumnCount π d σ v g (J i)-∑u∈J i,q u g|<((A i).card:ℝ)^(3/4:ℝ) ∧
      |rawIntervalStartColumnCount π d σ ((π^d).symm v) g (J i)-∑u∈J i,q u g/(d:ℝ)|<((A i).card:ℝ)^(3/4:ℝ)):=by
  obtain ⟨m,hm,hbudget⟩:=local_row_distinct_scales_error_budget 1 (δ/4) (by norm_num) (by linarith)
  refine ⟨m,hm,?_⟩
  intro V U Color _ _ _ _ _ I T A J hmin hinj hJ hJA π q hq hQ s hs hS hnoshort μ
  let t:=fun i:I=>((A i).card:ℝ)^(3/4:ℝ)
  have hA:∀i∈T,0<(A i).card:=by intro i hi;have:=hmin i hi;omega
  have ht:∀i∈T,0<t i:=by
    intro i hi
    dsimp [t]
    have hp:(0:ℝ)<(A i).card:=by exact_mod_cast hA i hi
    positivity
  have hsum:=hbudget I T (fun i=>(A i).card) (fun i=>(A i).card) hmin hinj (by intro i hi; simp)
  have hEach:∀i∈T,-2*(t i)^2/((A i).card:ℝ) = -2*((A i).card:ℝ)^(1/2:ℝ) :=by
    intro i hi
    have hp:(0:ℝ)<(A i).card:=by exact_mod_cast hA i hi
    have heq:(((A i).card:ℝ)^(3/4:ℝ))^2 = ((A i).card:ℝ)^(1/2:ℝ)*(A i).card := by
      calc
        _ = ((A i).card:ℝ)^((3/4:ℝ)*2) := by rw [Real.rpow_mul (le_of_lt hp)];norm_num
        _ = ((A i).card:ℝ)^(1/2:ℝ)*((A i).card:ℝ)^(1:ℝ) := by rw [← Real.rpow_add hp];norm_num
        _ = _ := by rw [Real.rpow_one]
    dsimp [t]
    rw [heq]
    field_simp
  have herror' : (∑i∈T,2*((A i).card:ℝ)*Real.exp (-2*(t i)^2/((A i).card:ℝ)))≤δ/4 :=by
    calc
      _ = ∑i∈T,2*((A i).card:ℝ)*Real.exp (-2*((A i).card:ℝ)^(1/2:ℝ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hEach i hi]
      _ ≤ δ/4 := hsum
  have herror : (∑i∈T,8*((A i).card:ℝ)*Real.exp (-2*(t i)^2/((A i).card:ℝ)))≤δ :=by
    have heq : (∑i∈T,8*((A i).card:ℝ)*Real.exp (-2*(t i)^2/((A i).card:ℝ))) =
        4*(∑i∈T,2*((A i).card:ℝ)*Real.exp (-2*(t i)^2/((A i).card:ℝ))) :=by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [heq]
    linarith
  have hh:=raw_interval_absorber_column_local_family_event π d hd q hq hQ s hs hS hnoshort I T A J t hJ hJA ht
  dsimp [t] at hh
  linarith
end Oberwolfach
