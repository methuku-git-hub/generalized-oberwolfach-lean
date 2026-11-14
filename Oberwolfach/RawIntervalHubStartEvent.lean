module

public import Oberwolfach.RawIntervalHubStartsSingleton
public import Oberwolfach.MarkedExpandedRawLaw
public import Oberwolfach.FiniteProductProjection
public import Oberwolfach.FiniteLawSigmaProjection

@[expose] public section
/-! Simultaneous hub-by-colour interval-count concentration, first in the
interval experiment and then on the full enriched retained exposure. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem rawIntervalHubStartCount_all_event
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hn:0<Fintype.card V) (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x) (t:ℝ) (ht:0<t):
    1-2*Fintype.card U*Fintype.card Γ*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(Fintype.card V:ℝ)))≤
    (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
      (fun σ=>∀ u g,|rawIntervalHubStartCount π d g σ u-(Fintype.card V:ℝ)*q u g/d|<t) := by
  let μ:=FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
  have hh:=finiteLaw_common_event_lower μ (Finset.univ:Finset (U×Γ))
    (fun z σ=>t≤|rawIntervalHubStartCount π d z.2 σ z.1-(Fintype.card V:ℝ)*q z.1 z.2/d|)
    (fun _=>2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(Fintype.card V:ℝ))))
    (fun z _=>by
      have ht':=rawIntervalHubStartCount_tail_singleton π d hd q hq hQ s hs hS hn z.2 z.1 t ht
      rw [rawIntervalHubStartCount_expectation π d hd q hq hQ s hs hS hnoshort z.1 z.2] at ht'
      exact ht')
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,nsmul_eq_mul,Nat.cast_mul,
    Finset.mem_univ,true_implies,not_le] at hh
  have hbudget:(Fintype.card U:ℝ)*Fintype.card Γ*(2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(Fintype.card V:ℝ))))=
      2*Fintype.card U*Fintype.card Γ*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(Fintype.card V:ℝ))):=by ring
  rw [hbudget] at hh
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ u g
  exact hσ (u,g)

theorem raw_expanded_marked_hub_starts_all_event (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hn:0<Fintype.card V) (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a)) (t:ℝ) (ht:0<t):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    1-2*Fintype.card U*Fintype.card Γ*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(Fintype.card V:ℝ)))≤
    (μ.sigma (fun ω=>ν (f ω))).probability
      (fun z=>∀ u g,|rawIntervalHubStartCount π d g (fun e=>z.1 (Sum.inr e)) u-(Fintype.card V:ℝ)*q u g/d|<t) := by
  intro μ f
  let E:=fun σ:∀ e:(U×RawIntervalCoordinate V),RawIntervalCoordinateState Γ Color e.2=>
    ∀ u g,|rawIntervalHubStartCount π d g σ u-(Fintype.card V:ℝ)*q u g/d|<t
  have hh:=rawIntervalHubStartCount_all_event π d hd q hq hQ s hs hS hn hnoshort t ht
  have heq:(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>E (fun e=>z.1 (Sum.inr e)))=
      (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability E:=by
    calc
      _ = μ.probability (fun ω=>E (fun e=>ω (Sum.inr e))) := finiteLaw_sigma_first_probability μ (fun ω=>ν (f ω)) _
      _ = _ := by
        simpa only [μ,rawExpandedMarkedWheelLaw] using
          (finiteLaw_pi_injective_projection_event
            (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
            Sum.inr Sum.inr_injective E)
  change 1-2*Fintype.card U*Fintype.card Γ*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(Fintype.card V:ℝ)))≤
    (μ.sigma (fun ω=>ν (f ω))).probability (fun z=>E (fun e=>z.1 (Sum.inr e)))
  rw [heq]
  exact hh
end Oberwolfach
