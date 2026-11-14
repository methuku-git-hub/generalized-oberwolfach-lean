module

public import Oberwolfach.MarkedExpandedRawLaw
public import Oberwolfach.RawStartCounts
public import Oberwolfach.FiniteProductProjection
public import Oberwolfach.FiniteLawSigmaProjection

@[expose] public section
/-! Simultaneous raw start counts for every colour, including colour 2 with
hub-dependent probabilities, on the full refined exposure. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem raw_interval_all_colours_starts_event (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x) (t:ℝ) (ht:0<t):
    1-2*Fintype.card Γ*Fintype.card V*Real.exp (-2*t^2/Fintype.card U)≤
    (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
      (fun σ=>∀ g a,|((rawStartHubSet π d σ g a).card:ℝ)-(∑ u,q u g/(d:ℝ))|<t) := by
  let μ:=FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
  have hh:=finiteLaw_common_event_lower μ (Finset.univ:Finset (Γ×V))
    (fun z σ=>t≤|((rawStartHubSet π d σ z.1 z.2).card:ℝ)-(∑ u,q u z.1/(d:ℝ))|)
    (fun _=>2*Real.exp (-2*t^2/Fintype.card U))
    (fun z _=>rawStartHubSet_tail π d hd q hq hQ s hs hS hnoshort z.1 z.2 t ht.le)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,nsmul_eq_mul,Nat.cast_mul,
    Finset.mem_univ,true_implies,not_le] at hh
  have hbudget:(Fintype.card Γ:ℝ)*Fintype.card V*(2*Real.exp (-2*t^2/Fintype.card U))=
      2*Fintype.card Γ*Fintype.card V*Real.exp (-2*t^2/Fintype.card U):=by ring
  rw [hbudget] at hh
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ g a
  exact hσ (g,a)

theorem raw_expanded_marked_all_colours_starts_event (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a)) (t:ℝ) (ht:0<t):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    1-2*Fintype.card Γ*Fintype.card V*Real.exp (-2*t^2/Fintype.card U)≤
    (μ.sigma (fun ω=>ν (f ω))).probability
      (fun z=>∀ g a,|((rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g a).card:ℝ)-(∑ u,q u g/(d:ℝ))|<t) := by
  intro μ f
  let E:=fun σ:∀ e:(U×RawIntervalCoordinate V),RawIntervalCoordinateState Γ Color e.2=>
    ∀ g a,|((rawStartHubSet π d σ g a).card:ℝ)-(∑ u,q u g/(d:ℝ))|<t
  have hh:=raw_interval_all_colours_starts_event π d hd q hq hQ s hs hS hnoshort t ht
  have heq:(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>E (fun e=>z.1 (Sum.inr e)))=
      (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability E:=by
    calc
      _ = μ.probability (fun ω=>E (fun e=>ω (Sum.inr e))) := finiteLaw_sigma_first_probability μ (fun ω=>ν (f ω)) _
      _ = _ := by
        simpa only [μ,rawExpandedMarkedWheelLaw] using
          (finiteLaw_pi_injective_projection_event
            (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
            Sum.inr Sum.inr_injective E)
  change 1-2*Fintype.card Γ*Fintype.card V*Real.exp (-2*t^2/Fintype.card U)≤
    (μ.sigma (fun ω=>ν (f ω))).probability (fun z=>E (fun e=>z.1 (Sum.inr e)))
  rw [heq]
  exact hh
end Oberwolfach
