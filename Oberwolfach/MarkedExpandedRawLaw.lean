module

public import Oberwolfach.MarkedExpandedPhysicalLaw
public import Oberwolfach.RawMarkedPotentialSampling

@[expose] public section
/-! Refine each physical coordinate while retaining every original raw
interval coordinate and its law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

abbrev RawExpandedMarkedCoordinateState (Γ Color:Type):RawWheelCoordinate V U→Type
  | Sum.inl _=>Fin 6×Bool
  | Sum.inr e=>RawIntervalCoordinateState Γ Color e.2

instance rawExpandedMarkedCoordinateFintype (e:RawWheelCoordinate V U):
    Fintype (RawExpandedMarkedCoordinateState Γ Color e):=by
  cases e with
  | inl e=>exact inferInstanceAs (Fintype (Fin 6×Bool))
  | inr e=>exact inferInstanceAs (Fintype (RawIntervalCoordinateState Γ Color e.2))

def rawExpandedMarkedCollapse (e:RawWheelCoordinate V U):
    RawExpandedMarkedCoordinateState Γ Color e→RawMarkedCoordinateState Γ Color e:=
  match e with
  | Sum.inl _=>markedExpandedPhysicalCollapse
  | Sum.inr _=>id

def rawExpandedMarkedWheelLaw
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g)):
    ∀ e:RawWheelCoordinate V U,FiniteLaw (RawExpandedMarkedCoordinateState Γ Color e)
  | Sum.inl _=>FiniteLaw.categoricalDirection (markedExpandedPhysicalProbability p k p₂ k₂ u)
      (markedExpandedPhysicalProbability_nonneg p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum)
      (markedExpandedPhysicalProbability_sum p k p₂ k₂ u)
  | Sum.inr e=>rawIntervalFamilyLaw d hd q hq hQ s hs hS e

theorem raw_expanded_marked_wheel_law_projection
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g)):
    (FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)).map
      (fun σ e=>rawExpandedMarkedCollapse e (σ e)) =
    FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p k hp hk (by linarith) d hd q hq hQ s hs hS) := by
  rw [finiteLaw_pi_map]
  congr 1
  funext e
  cases e with
  | inl e=>
    exact marked_expanded_physical_collapse_law p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum
  | inr e=>
    apply finiteLaw_ext
    intro z
    simp [FiniteLaw.map,rawExpandedMarkedCollapse,rawExpandedMarkedWheelLaw,rawMarkedWheelLaw]
end Oberwolfach
