module

public import Oberwolfach.MarkedExpandedRawLaw
public import Oberwolfach.FiniteLawSigmaProjection

@[expose] public section
/-! Forgetting selected and unassigned physical states gives exactly the
raw approximate-layer law, while retaining the original interval variables. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def markedExpandedApproximateCollapse (z:Fin 6×Bool):Option (Bool×Bool):=
  if z.1=2 then some (false,z.2) else if z.1=3 then some (true,z.2) else none

theorem marked_expanded_approximate_physical_law
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1):
    (FiniteLaw.categoricalDirection (markedExpandedPhysicalProbability p k p₂ k₂ u)
      (markedExpandedPhysicalProbability_nonneg p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum)
      (markedExpandedPhysicalProbability_sum p k p₂ k₂ u)).map markedExpandedApproximateCollapse=
      markedPhysicalLaw p₂ k₂ hp₂ hk₂ (by linarith) := by
  apply finiteLaw_ext
  intro z
  cases z with
  | none=>
    simp [FiniteLaw.map,FiniteLaw.categoricalDirection,markedExpandedPhysicalProbability,
      markedExpandedApproximateCollapse,markedPhysicalLaw,Fintype.sum_prod_type,Fin.sum_univ_succ,Fintype.sum_bool]
    ring
  | some z=>
    rcases z with ⟨b,c⟩
    cases b <;> cases c <;>
      simp [FiniteLaw.map,FiniteLaw.categoricalDirection,markedExpandedPhysicalProbability,
        markedExpandedApproximateCollapse,markedPhysicalLaw,Fintype.sum_prod_type,Fin.sum_univ_succ,Fintype.sum_bool]

variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def rawExpandedApproximateCollapse (e:RawWheelCoordinate V U):
    RawExpandedMarkedCoordinateState Γ Color e→RawMarkedCoordinateState Γ Color e:=
  match e with
  | Sum.inl _=>markedExpandedApproximateCollapse
  | Sum.inr _=>id

theorem raw_expanded_approximate_wheel_law_projection
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g)):
    (FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)).map
      (fun σ e=>rawExpandedApproximateCollapse e (σ e)) =
    FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p₂ k₂ hp₂ hk₂ (by linarith) d hd q hq hQ s hs hS) := by
  rw [finiteLaw_pi_map]
  congr 1
  funext e
  cases e with
  | inl e=>exact marked_expanded_approximate_physical_law p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum
  | inr e=>
    apply finiteLaw_ext
    intro z
    simp [FiniteLaw.map,rawExpandedApproximateCollapse,rawExpandedMarkedWheelLaw,rawMarkedWheelLaw]

theorem raw_expanded_approximate_probability_after_retention
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a))
    (E:RawMarkedOutcome V U Γ Color→Prop):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    (μ.sigma (fun ω=>ν (f ω))).probability (fun z=>E (fun e=>rawExpandedApproximateCollapse e (z.1 e)))=
      (FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p₂ k₂ hp₂ hk₂ (by linarith) d hd q hq hQ s hs hS)).probability E:=by
  intro μ f
  calc
    _ = μ.probability (fun ω=>E (fun e=>rawExpandedApproximateCollapse e (ω e))) := finiteLaw_sigma_first_probability μ (fun ω=>ν (f ω)) _
    _ = _ := by rw [←finiteLaw_map_probability,raw_expanded_approximate_wheel_law_projection p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum]
end Oberwolfach
