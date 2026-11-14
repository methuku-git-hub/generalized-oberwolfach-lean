module

public import Oberwolfach.RawUnassignedHubLocalSmallFailure
public import Oberwolfach.RawIntervalUnassignedCountsEvent

@[expose] public section
/-! The local unassigned-spoke rows lift to the expanded sample and any retained fiber. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_expanded_unassigned_hub_local_family_small_failure
    (d:ℕ) (hd:2≤d) (C δ:ℝ) (hC:0≤C) (hδ:0<δ) :
    ∃m:ℕ,1≤m ∧ ∀(V U Γ Color:Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
      [Fintype Γ] [Fintype Color],
    ∀(I:Type) (T:Finset I) (A:I→Finset V) (B:I→Finset U),
    (∀i∈T,m≤(A i).card) → Set.InjOn (fun i=>(A i).card) T →
    (∀i∈T,((B i).card:ℝ)≤C*(A i).card) →
    ∀(π:Equiv.Perm V) (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a)),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    1-δ≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>∀i∈T,∀w∈B i,
      |rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) w (A i)-
      ((A i).card:ℝ)*(1-(∑g,q w g)-(∑j,s w j))|<((A i).card:ℝ)^(3/4:ℝ)):=by
  obtain ⟨m,hm,hfamily⟩:=raw_interval_unassigned_hub_local_family_small_failure d hd C δ hC hδ
  refine ⟨m,hm,?_⟩
  intro V U Γ Color _ _ _ _ _ _ I T A B hmin hinj hB π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort F _ ν μ f
  let E:=fun σ:RawIntervalFamilyOutcome V U Γ Color=>∀i∈T,∀w∈B i,
    |rawIntervalUnassignedHubCountOn π d σ w (A i)-
      ((A i).card:ℝ)*(1-(∑g,q w g)-(∑j,s w j))|<((A i).card:ℝ)^(3/4:ℝ)
  have hh:=hfamily V U Γ Color I T A B hmin hinj hB π q hq hQ s hs hS hnoshort
  have heq:(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>E (fun e=>z.1 (Sum.inr e)))=
      (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability E:=by
    calc
      _ = μ.probability (fun ω=>E (fun e=>ω (Sum.inr e))) := finiteLaw_sigma_first_probability μ (fun ω=>ν (f ω)) _
      _ = _ := by
        simpa only [μ,rawExpandedMarkedWheelLaw] using
          (finiteLaw_pi_injective_projection_event
            (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
            Sum.inr Sum.inr_injective E)
  change 1-δ≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>E (fun e=>z.1 (Sum.inr e)))
  rw [heq]
  exact hh
end Oberwolfach
