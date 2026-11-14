module

public import Oberwolfach.RawVariableSpokeHubCounts
public import Oberwolfach.OrdinaryRawIntervalSampling
public import Oberwolfach.FiniteProductProjection

@[expose] public section
/-! Simultaneous concentration of each reserved-spoke column under the
    original ordinary sample, retaining hub-specific probabilities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_reference_spoke_columns_high_probability
    (π:Equiv.Perm V) (p:ℝ) (hp:0≤p) (hp1:p≤1) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x) (hn:0<Fintype.card V)
    (g:Γ) (j:Color) (t:ℝ) (ht:0<t):
    1-4*(Fintype.card U:ℝ)*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(Fintype.card V)))≤
      (FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>p) (fun _=>hp) (fun _=>hp1) d hd q hq hQ s hs hS)).probability
      (fun σ=>∀u,|((Finset.univ.filter (fun v=>rawWheelSpokes π d σ j v u)).card:ℝ)-s u j*Fintype.card V|<t):=by
  have hh:=raw_variable_spoke_hub_counts_event π d hd q hq hQ s hs hS hnoshort hn g j t ht
  have hproj:=finiteLaw_pi_injective_projection_event
    (rawWheelLaw (V:=V) (fun _=>p) (fun _=>hp) (fun _=>hp1) d hd q hq hQ s hs hS) Sum.inr Sum.inr_injective
    (fun σ=>∀b u,|rawMarkedRestrictedSpokeCol π d σ g j b u Finset.univ-
      (if b then q u g else s u j)*(Fintype.card V:ℝ)|<t)
  simp only [rawWheelLaw] at hproj
  rw [←hproj] at hh
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ u
  have hc:=hσ false u
  rw [raw_spoke_hub_count_eq_card] at hc
  simpa only [Bool.false_eq_true,ite_false,rawMarkedSpokes,rawWheelSpokes] using hc
end Oberwolfach
