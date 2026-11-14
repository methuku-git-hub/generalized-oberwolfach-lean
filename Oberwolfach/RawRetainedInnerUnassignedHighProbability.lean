module

public import Oberwolfach.RawUnassignedAdaptiveHighProbability
public import Oberwolfach.MarkedExpandedRetainedProjection
public import Oberwolfach.RawMarkedRetention

@[expose] public section
/-! The fixed inner vertex set can be included in the same retained sample's
unassigned-row tests, with arbitrarily small error probability. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_retained_inner_unassigned_high_probability
    (d:ℕ) (hd:2≤d) (δ:ℝ) (hδ:0<δ):
    ∃N:ℕ,∀(V:Type) [Fintype V] [LinearOrder V] [Nonempty V],N≤Fintype.card V→
    ∀(U Γ Color:Type) [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color],
    Fintype.card U≤Fintype.card V→
    ∀(π:Equiv.Perm V) (g₀:Γ) (p k:ℝ) (hp:0≤p) (hk:0≤k) (hphys:2*p+2*k≤1)
    (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,(∑ g:Γ, q w g)≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,(∑ j:Color, s w j)≤ intervalUncoveredProbability d (∑ g:Γ, q w g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x) (vertices:Finset V),
    1-δ≤(rawMarkedRetentionLaw π d hd g₀ p k hp hk hphys q hq hQ s hs hS).probability (fun z=>
      ∀w,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) w vertices-
        (vertices.card:ℝ)*(1-(∑ g:Γ, q w g)-(∑ j:Color, s w j))|<(Fintype.card V:ℝ)^(3/4:ℝ)):=by
  obtain ⟨N₀,hN₀⟩:=raw_unassigned_physical_adaptive_high_probability d hd δ hδ
  refine ⟨max N₀ 1,?_⟩
  intro V _ _ _ hn U Γ Color _ _ _ _ hUV π g₀ p k hp hk hphys q hq hQ s hs hS hnoshort vertices
  have hn0:0<Fintype.card V:=by omega
  have hI:Fintype.card Unit≤4*(Fintype.card V)^2:=by simp; nlinarith
  let F:=fun raw:RawMarkedOutcome V U Γ Color=>StartRetentionOutcome
    (rawStartHubSet π d (fun e=>raw (Sum.inr e)) g₀)
    (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) g₀))
  let ν:=fun raw:RawMarkedOutcome V U Γ Color=>startRetentionLaw
    (rawStartHubSet π d (fun e=>raw (Sum.inr e)) g₀)
    (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) g₀)) (startRetentionMinimum_le _)
  let E:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d g₀→Prop:=fun z=>
    ∀w,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) w vertices-
      (vertices.card:ℝ)*(1-(∑ g:Γ, q w g)-(∑ j:Color, s w j))|<(Fintype.card V:ℝ)^(3/4:ℝ)
  have hsum:2*p+2*k+2*(0:ℝ)+2*0+0≤1:=by linarith
  have hp0:=hN₀ V (by omega) U Γ Color Unit hUV hI π p k 0 0 0 hp hk (by norm_num) (by norm_num) (by norm_num) hsum
    q hq hQ s hs hS hnoshort (fun _ _=>vertices) F ν
  have hproj:=raw_expanded_marked_retained_projection_probability p k 0 0 0 hp hk (by norm_num) (by norm_num) (by norm_num) hsum d hd q hq hQ s hs hS F ν E
  change 1-δ≤(rawMarkedRetentionLaw π d hd g₀ p k hp hk hphys q hq hQ s hs hS).probability E
  unfold rawMarkedRetentionLaw
  change 1-δ≤((FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hphys d hd q hq hQ s hs hS)).sigma ν).probability E
  rw [←hproj]
  simpa [E,rawExpandedMarkedCollapse] using hp0
end Oberwolfach
