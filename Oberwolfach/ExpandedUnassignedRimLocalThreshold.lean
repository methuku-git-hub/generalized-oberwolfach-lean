module

public import Oberwolfach.LocalRowBudgetThreshold
public import Oberwolfach.ExpandedUnassignedRimLocalExtra
public import Oberwolfach.LocalRowFamilyErrorBudget

@[expose] public section
/-! Uniformly many distinct local scales have an arbitrarily small total failure budget. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
theorem raw_expanded_unassigned_rim_local_family_threshold
    (C δ:ℝ) (hC:0≤C) (hδ:0<δ) :
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U], ∀(G:SimpleGraph V) (I:Type) (T:Finset I) (A B:I→Finset V),
    (∀i∈T,localRowBudgetThreshold C δ hC hδ≤(A i).card) → Set.InjOn (fun i=>(A i).card) T →
    (∀i∈T,((B i).card:ℝ)≤C*(A i).card) →
    ∀ (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)]
    (ν:∀ a,FiniteLaw (F a)),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    ∀ (Extra:(Σω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,F (f ω))→Prop) (ξ:ℝ),
    1-ξ≤(μ.sigma (fun ω=>ν (f ω))).probability Extra →
    1-ξ-δ≤
    (μ.sigma (fun ω=>ν (f ω))).probability (fun z=>Extra z ∧ ∀ i∈T,∀ x∈B i,
      |(((G.neighborFinset x∩A i).filter (fun y=>(z.1 (Sum.inl s(x,y))).1=4)).card:ℝ)-
        u*(G.neighborFinset x∩A i).card|<((A i).card:ℝ)^(3/4:ℝ))   :=by
  have hspec:=localRowBudgetThreshold_spec C δ hC hδ
  have hm:=hspec.1
  have hbudget:=hspec.2
  intro V U Γ Color _ _ _ _ _ _ G I T A B hmin hinj hB p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F _ ν μ f Extra ξ hExtra
  let t:=fun i:I=>((A i).card:ℝ)^(3/4:ℝ)
  have ht:∀i∈T,0<t i:=by
    intro i hi
    dsimp [t]
    have hp:(0:ℝ)<(A i).card:=by exact_mod_cast (show 0<(A i).card by have:=hmin i hi;omega)
    positivity
  have hbudgetSum:=hbudget I T (fun i=>(A i).card) (fun i=>(B i).card) hmin hinj hB
  have hEach:∀i∈T, -2*(t i)^2/((A i).card:ℝ) = -2*((A i).card:ℝ)^(1/2:ℝ) :=by
    intro i hi
    have hp:(0:ℝ)<(A i).card:=by exact_mod_cast (show 0<(A i).card by have:=hmin i hi;omega)
    have heq:(((A i).card:ℝ)^(3/4:ℝ))^2 = ((A i).card:ℝ)^(1/2:ℝ)*(A i).card := by
      calc
        _ = ((A i).card:ℝ)^((3/4:ℝ)*2) := by rw [Real.rpow_mul (le_of_lt hp)];norm_num
        _ = ((A i).card:ℝ)^(1/2:ℝ)*((A i).card:ℝ)^(1:ℝ) := by rw [← Real.rpow_add hp];norm_num
        _ = _ := by rw [Real.rpow_one]
    dsimp [t]
    rw [heq]
    field_simp
  have herror : (∑i∈T,2*((B i).card:ℝ)*Real.exp (-2*(t i)^2/((A i).card:ℝ)))≤δ :=by
    calc
      _ = ∑i∈T,2*((B i).card:ℝ)*Real.exp (-2*((A i).card:ℝ)^(1/2:ℝ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hEach i hi]
      _ ≤ δ := hbudgetSum
  have hcommon:=raw_expanded_unassigned_rim_local_family_with_extra G I T A B p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F ν t ht Extra ξ hExtra
  dsimp [t] at hcommon
  linarith
end Oberwolfach
