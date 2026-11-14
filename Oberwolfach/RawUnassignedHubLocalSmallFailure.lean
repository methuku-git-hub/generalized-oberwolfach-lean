module

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

theorem raw_interval_unassigned_hub_local_family_small_failure
    (d:ℕ) (hd:2≤d) (C δ:ℝ) (hC:0≤C) (hδ:0<δ) :
    ∃m:ℕ,1≤m ∧ ∀(V U Γ Color:Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
      [Fintype Γ] [Fintype Color],
    ∀(I:Type) (T:Finset I) (A:I→Finset V) (B:I→Finset U),
    (∀i∈T,m≤(A i).card) → Set.InjOn (fun i=>(A i).card) T →
    (∀i∈T,((B i).card:ℝ)≤C*(A i).card) →
    ∀(π:Equiv.Perm V) (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x),
    let μ:=FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
    1-δ≤μ.probability (fun σ=>∀i∈T,∀u∈B i,|rawIntervalUnassignedHubCountOn π d σ u (A i)-
      ((A i).card:ℝ)*(1-(∑g,q u g)-(∑j,s u j))|<((A i).card:ℝ)^(3/4:ℝ)):=by
  let c:ℝ:=2/(4*(d:ℝ)+3)^2
  have hc:0<c:=by dsimp [c];positivity
  obtain ⟨m,hm,hbudget⟩:=local_row_distinct_scales_general_error_budget C c δ hC hc hδ
  refine ⟨m,hm,?_⟩
  intro V U Γ Color _ _ _ _ _ _ I T A B hmin hinj hB π q hq hQ s hs hS hnoshort μ
  let t:=fun i:I=>((A i).card:ℝ)^(3/4:ℝ)
  have hA:∀i∈T,0<(A i).card:=by intro i hi;have:=hmin i hi;omega
  have ht:∀i∈T,0<t i:=by
    intro i hi
    dsimp [t]
    have hp:(0:ℝ)<(A i).card:=by exact_mod_cast hA i hi
    positivity
  have hsum:=hbudget I T (fun i=>(A i).card) (fun i=>(B i).card) hmin hinj hB
  have hEach:∀i∈T,-2*(t i)^2/((4*(d:ℝ)+3)^2*((A i).card:ℝ)) = -c*((A i).card:ℝ)^(1/2:ℝ) :=by
    intro i hi
    have hp:(0:ℝ)<(A i).card:=by exact_mod_cast hA i hi
    have heq:(((A i).card:ℝ)^(3/4:ℝ))^2 = ((A i).card:ℝ)^(1/2:ℝ)*(A i).card := by
      calc
        _ = ((A i).card:ℝ)^((3/4:ℝ)*2) := by rw [Real.rpow_mul (le_of_lt hp)];norm_num
        _ = ((A i).card:ℝ)^(1/2:ℝ)*((A i).card:ℝ)^(1:ℝ) := by rw [← Real.rpow_add hp];norm_num
        _ = _ := by rw [Real.rpow_one]
    dsimp [t,c]
    rw [heq]
    field_simp
  have herror : (∑i∈T,2*((B i).card:ℝ)*Real.exp (-2*(t i)^2/((4*(d:ℝ)+3)^2*((A i).card:ℝ))))≤δ :=by
    calc
      _ = ∑i∈T,2*((B i).card:ℝ)*Real.exp (-c*((A i).card:ℝ)^(1/2:ℝ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hEach i hi]
      _ ≤ δ := hsum
  have hh:=raw_interval_unassigned_hub_local_family_event π d hd q hq hQ s hs hS hnoshort I T A B t hA ht
  dsimp [t] at hh
  linarith
end Oberwolfach
