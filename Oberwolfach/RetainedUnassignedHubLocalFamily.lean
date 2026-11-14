module

public import Oberwolfach.ExpandedUnassignedHubLocalSmallFailure
public import Oberwolfach.MarkedExpandedRetainedProjection
public import Oberwolfach.RawMarkedRetention

@[expose] public section
/-! Local spoke rows remain high probability after the original retention. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_retained_unassigned_hub_local_family_small_failure
    (d:ℕ) (hd:2≤d) (C δ:ℝ) (hC:0≤C) (hδ:0<δ) :
    ∃m:ℕ,1≤m ∧ ∀(V U Γ Color:Type) [Fintype V] [LinearOrder V] [Nonempty V]
      [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color],
    ∀(I:Type) (T:Finset I) (A:I→Finset V) (B:I→Finset U),
    (∀i∈T,m≤(A i).card) → Set.InjOn (fun i=>(A i).card) T →
    (∀i∈T,((B i).card:ℝ)≤C*(A i).card) →
    ∀(π:Equiv.Perm V) (g₀:Γ) (p k:ℝ) (hp:0≤p) (hk:0≤k) (hphys:2*p+2*k≤1)
    (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x),
    1-δ≤(rawMarkedRetentionLaw π d hd g₀ p k hp hk hphys q hq hQ s hs hS).probability
      (fun z=>∀i∈T,∀w∈B i,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) w (A i)-
        ((A i).card:ℝ)*(1-(∑g,q w g)-(∑j,s w j))|<((A i).card:ℝ)^(3/4:ℝ)):=by
  obtain ⟨m,hm,hExpanded⟩:=raw_expanded_unassigned_hub_local_family_small_failure d hd C δ hC hδ
  refine ⟨m,hm,?_⟩
  intro V U Γ Color _ _ _ _ _ _ _ I T A B hmin hinj hB π g₀ p k hp hk hphys q hq hQ s hs hS hnoshort
  let F:=fun raw:RawMarkedOutcome V U Γ Color=>StartRetentionOutcome
    (rawStartHubSet π d (fun e=>raw (Sum.inr e)) g₀)
    (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) g₀))
  let ν:=fun raw:RawMarkedOutcome V U Γ Color=>startRetentionLaw
    (rawStartHubSet π d (fun e=>raw (Sum.inr e)) g₀)
    (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) g₀)) (startRetentionMinimum_le _)
  let E:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d g₀=>
    ∀i∈T,∀w∈B i,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) w (A i)-
      ((A i).card:ℝ)*(1-(∑g,q w g)-(∑j,s w j))|<((A i).card:ℝ)^(3/4:ℝ)
  have hsum:2*p+2*k+2*(0:ℝ)+2*0+0≤1:=by linarith only [hphys]
  have hp0:=hExpanded V U Γ Color I T A B hmin hinj hB π p k 0 0 0 hp hk (by norm_num) (by norm_num) (by norm_num) hsum
    q hq hQ s hs hS hnoshort F ν
  have hproj:=raw_expanded_marked_retained_projection_probability p k 0 0 0 hp hk (by norm_num) (by norm_num) (by norm_num) hsum d hd q hq hQ s hs hS F ν E
  change 1-δ≤(rawMarkedRetentionLaw π d hd g₀ p k hp hk hphys q hq hQ s hs hS).probability E
  unfold rawMarkedRetentionLaw
  change 1-δ≤((FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hphys d hd q hq hQ s hs hS)).sigma ν).probability E
  rw [←hproj]
  simpa [E,rawExpandedMarkedCollapse] using hp0
end Oberwolfach
