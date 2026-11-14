module

public import Oberwolfach.OrdinaryRawIntervalSampling
public import Oberwolfach.RetainedGraphDegreeConcentration
public import Oberwolfach.FiniteProductProjection

@[expose] public section
/-! The sampled ordinary reference rim has simultaneous degree concentration
    under the original product law, with no independence assumption added. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_raw_reference_rim_degree_concentration
    (P:SimpleGraph V) (p t:ℝ) (hp:0≤p) (hp1:p≤1) (ht:0≤t)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g)):
    1-2*(Fintype.card V:ℝ)*Real.exp (-2*t^2/Fintype.card V)≤
      (FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>p) (fun _=>hp) (fun _=>hp1) d hd q hq hQ s hs hS)).probability
      (fun σ=>∀v,|((rawWheelGraph P σ).degree v:ℝ)-p*(P.degree v:ℝ)|<t):=by
  have hh:=retained_graph_degree_concentration P p t hp hp1 ht
  have hproj:=finiteLaw_pi_injective_projection_event
    (rawWheelLaw (V:=V) (fun _=>p) (fun _=>hp) (fun _=>hp1) d hd q hq hQ s hs hS) Sum.inl Sum.inl_injective
    (fun σ=>∀v,|((retainedGraph P σ).degree v:ℝ)-p*(P.degree v:ℝ)|<t)
  simp only [rawWheelGraph]
  rw [hproj]
  exact hh
end Oberwolfach
