module

public import Oberwolfach.PhysicalRestrictedLocalScale
public import Oberwolfach.ExpandedPhysicalRestrictedDegree
public import Oberwolfach.OrientationMargins

@[expose] public section
/-! Unassigned physical edges into a fixed set, for every ambient root,
on the original enriched exposure and after conditional retention. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem raw_expanded_unassigned_rim_degree_local_event
    (G:SimpleGraph V) (A B:Finset V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)]
    (ν:∀ a,FiniteLaw (F a)) (t:ℝ) (ht:0<t):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    1-2*(B.card:ℝ)*Real.exp (-2*t^2/(A.card:ℝ))≤
    (μ.sigma (fun ω=>ν (f ω))).probability (fun z=>∀ x∈B,
      |(((G.neighborFinset x∩A).filter (fun y=>(z.1 (Sum.inl s(x,y))).1=4)).card:ℝ)-
        u*(G.neighborFinset x∩A).card|<t):=by
  intro μ f
  let ρ:=markedExpandedPhysicalProbability p k p₂ k₂ u
  let E:=fun σ:Sym2 V→Fin 6×Bool=>∀ x∈B,
    |(((G.neighborFinset x∩A).filter (fun y=>(σ s(x,y)).1=4)).card:ℝ)-u*(G.neighborFinset x∩A).card|<t
  have hh:=physicalRestrictedColourDegree_local_event G A B ρ
    (markedExpandedPhysicalProbability_nonneg p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum)
    (markedExpandedPhysicalProbability_sum p k p₂ k₂ u) 4 t ht
  have hh':1-2*(B.card:ℝ)*Real.exp (-2*t^2/(A.card:ℝ))≤
    (FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.categoricalDirection ρ
      (markedExpandedPhysicalProbability_nonneg p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum)
      (markedExpandedPhysicalProbability_sum p k p₂ k₂ u))).probability E:=by
    simpa [E,ρ,markedExpandedPhysicalProbability] using hh
  have heq:(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>E (fun e=>z.1 (Sum.inl e)))=
    (FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.categoricalDirection ρ
      (markedExpandedPhysicalProbability_nonneg p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum)
      (markedExpandedPhysicalProbability_sum p k p₂ k₂ u))).probability E:=by
    calc
      _ = μ.probability (fun ω=>E (fun e=>ω (Sum.inl e))) := finiteLaw_sigma_first_probability μ (fun ω=>ν (f ω)) _
      _ = _ := by
        simpa only [μ,rawExpandedMarkedWheelLaw] using
          (finiteLaw_pi_injective_projection_event
            (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
            Sum.inl Sum.inl_injective E)
  change 1-2*(B.card:ℝ)*Real.exp (-2*t^2/(A.card:ℝ))≤
    (μ.sigma (fun ω=>ν (f ω))).probability (fun z=>E (fun e=>z.1 (Sum.inl e)))
  rw [heq]
  exact hh'
end Oberwolfach
