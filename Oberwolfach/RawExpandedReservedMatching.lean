module

public import Oberwolfach.RawIntervalActualReservedMatching
public import Oberwolfach.RawIntervalUnassignedCountsEvent

@[expose] public section
/-! The same all-pairs event holds on the full physical experiment and after
any conditional retention; its universal quantifiers permit later choices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem raw_expanded_reserved_matching_common_event
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (F:RawMarkedOutcome V U Γ Color→Type) [∀a,Fintype (F a)] (ν:∀a,FiniteLaw (F a))
    (hm:0<Fintype.card U) (j:Color) (s₀:ℝ) (hs₀:0≤s₀) (hsl:∀u,s₀≤s u j)
    (t α:ℝ) (ht:0<t)
    (hmargin:2*α*Fintype.card V+t≤(5/8:ℝ)*s₀^2*Fintype.card U):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    1-(Fintype.card V:ℝ)^2*(2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(2*Fintype.card U))))≤
    (μ.sigma (fun ω=>ν (f ω))).probability (fun z=>
      rawIntervalReservedMatchingEvent π d (fun e=>z.1 (Sum.inr e)) j α) :=by
  intro μ f
  let E:=fun σ:RawIntervalFamilyOutcome V U Γ Color=>rawIntervalReservedMatchingEvent π d σ j α
  have hh:=raw_interval_actual_reserved_matching_common_event π d hd q hq hQ s hs hS hnoshort hm j s₀ hs₀ hsl t α ht hmargin
  have heq:(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>E (fun e=>z.1 (Sum.inr e)))=
      (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability E:=by
    calc
      _ = μ.probability (fun ω=>E (fun e=>ω (Sum.inr e))) := finiteLaw_sigma_first_probability μ (fun ω=>ν (f ω)) _
      _ = _ := by
        simpa only [μ,rawExpandedMarkedWheelLaw] using
          (finiteLaw_pi_injective_projection_event
            (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
            Sum.inr Sum.inr_injective E)
  change 1-(Fintype.card V:ℝ)^2*(2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(2*Fintype.card U))))≤
    (μ.sigma (fun ω=>ν (f ω))).probability (fun z=>E (fun e=>z.1 (Sum.inr e)))
  rw [heq]
  exact hh

theorem raw_expanded_reserved_matching_with_event
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (F:RawMarkedOutcome V U Γ Color→Type) [∀a,Fintype (F a)] (ν:∀a,FiniteLaw (F a))
    (hm:0<Fintype.card U) (j:Color) (s₀:ℝ) (hs₀:0≤s₀) (hsl:∀u,s₀≤s u j)
    (t α:ℝ) (ht:0<t)
    (hmargin:2*α*Fintype.card V+t≤(5/8:ℝ)*s₀^2*Fintype.card U):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    let μret:=μ.sigma (fun ω=>ν (f ω));
    ∀ (E:(Σω,F (f ω))→Prop) (ε:ℝ),1-ε≤μret.probability E→
    1-ε-(Fintype.card V:ℝ)^2*(2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(2*Fintype.card U))))≤
    μret.probability (fun z=>E z ∧ rawIntervalReservedMatchingEvent π d (fun e=>z.1 (Sum.inr e)) j α) :=by
  intro μ f μret E ε hE
  have hA:=raw_expanded_reserved_matching_common_event π d hd p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort F ν hm j s₀ hs₀ hsl t α ht hmargin
  have hi:=finiteLaw_good_intersection μret E
    (fun z=>rawIntervalReservedMatchingEvent π d (fun e=>z.1 (Sum.inr e)) j α)
    ((Fintype.card V:ℝ)^2*(2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(2*Fintype.card U)))) ) hA
  linarith

end Oberwolfach
