module

public import Oberwolfach.RawExpandedReservedMatching
public import Oberwolfach.RawIntervalCodegreeMargin

@[expose] public section
/-! Choose the codegree constant before n and add the reservation event to
any existing common event on the same retained physical experiment. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_expanded_reserved_matching_high_probability
    (d:ℕ) (hd:2≤d) (ω s₀ ζ:ℝ) (hω:0<ω) (hs₀:0<s₀) (hζ:0<ζ):
    ∃ α:ℝ,α=(5/32:ℝ)*s₀^2*ω ∧ 0<α ∧ ∃ N:ℕ,∀ (V U Γ Color:Type)
      [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color],
      N≤Fintype.card V→ω*(Fintype.card V:ℝ)≤Fintype.card U→
    ∀ (π:Equiv.Perm V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (F:RawMarkedOutcome V U Γ Color→Type) [∀a,Fintype (F a)] (ν:∀a,FiniteLaw (F a))
    (j:Color) (hsl:∀u,s₀≤s u j),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (σ e)
    let μret:=μ.sigma (fun σ=>ν (f σ));
    (1-ζ≤μret.probability (fun z=>rawIntervalReservedMatchingEvent π d (fun e=>z.1 (Sum.inr e)) j α)) ∧
    (∀ (E:(Σσ,F (f σ))→Prop) (ε:ℝ),1-ε≤μret.probability E→
      1-ε-ζ≤μret.probability (fun z=>E z ∧ rawIntervalReservedMatchingEvent π d (fun e=>z.1 (Sum.inr e)) j α)) :=by
  let α:ℝ:=(5/32:ℝ)*s₀^2*ω
  have hα:0<α:=by dsimp [α];positivity
  obtain ⟨N,hN⟩:=raw_interval_codegree_margin d ω s₀ ζ hω hs₀ hζ
  refine ⟨α,rfl,hα,max N 1,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hmn π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort F _ ν j hsl μ f μret
  have hnN:N≤Fintype.card V:=le_trans (le_max_left _ _) hn
  have hnpos:(0:ℝ)<Fintype.card V:=by exact_mod_cast (show 0<Fintype.card V by have h:=le_trans (le_max_right N 1) hn;omega)
  have hmpos:(0:ℝ)<Fintype.card U:=lt_of_lt_of_le (mul_pos hω hnpos) hmn
  have hm:0<Fintype.card U:=by exact_mod_cast hmpos
  let t:ℝ:=(5/16:ℝ)*s₀^2*Fintype.card U
  have hb:=hN (Fintype.card V) (Fintype.card U) hnN hmn
  have ht:0<t:=hb.1
  have hmarg:2*α*Fintype.card V+t≤(5/8:ℝ)*s₀^2*Fintype.card U:=hb.2.2.1
  have herr:(Fintype.card V:ℝ)^2*(2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(2*Fintype.card U))))≤ζ:=hb.2.2.2
  have hA:=raw_expanded_reserved_matching_common_event π d hd p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort F ν hm j s₀ hs₀.le hsl t α ht hmarg
  have hprob:1-ζ≤μret.probability (fun z=>rawIntervalReservedMatchingEvent π d (fun e=>z.1 (Sum.inr e)) j α):=by linarith
  refine ⟨hprob,?_⟩
  intro E ε hE
  have hh:=finiteLaw_good_intersection μret E
    (fun z=>rawIntervalReservedMatchingEvent π d (fun e=>z.1 (Sum.inr e)) j α) ζ hprob
  linarith
end Oberwolfach
