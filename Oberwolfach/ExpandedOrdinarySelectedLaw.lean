module

public import Oberwolfach.MarkedExpandedRawLaw
public import Oberwolfach.OrdinaryRawIntervalSampling

@[expose] public section
/-! Forget the direction and retain precisely the selected ordinary physical
state; interval coordinates and their original law are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

def expandedOrdinarySelectedCollapse (e:RawWheelCoordinate V U):
    RawExpandedMarkedCoordinateState Γ Color e→RawWheelCoordinateState Γ Color e:=
  match e with
  | Sum.inl _=>fun z=>decide (z.1=0)
  | Sum.inr _=>id

theorem expanded_ordinary_selected_physical_law
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1):
    (FiniteLaw.categoricalDirection (markedExpandedPhysicalProbability p k p₂ k₂ u)
      (markedExpandedPhysicalProbability_nonneg p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum)
      (markedExpandedPhysicalProbability_sum p k p₂ k₂ u)).map (fun z=>decide (z.1=0))=
      FiniteLaw.retentionCoin (2*p) (by linarith) (by linarith) := by
  apply finiteLaw_ext
  intro b
  cases b <;> simp [FiniteLaw.map,FiniteLaw.categoricalDirection,markedExpandedPhysicalProbability,
    FiniteLaw.retentionCoin,Fintype.sum_prod_type,Fin.sum_univ_succ,Fintype.sum_bool] <;> ring

theorem expanded_ordinary_selected_wheel_law
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
    (hS:∀ u,∑ j,s u j ≤ intervalUncoveredProbability d (∑ g,q u g)):
    (FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)).map
      (fun σ e=>expandedOrdinarySelectedCollapse e (σ e)) =
    FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>2*p) (fun _=>by linarith) (fun _=>by linarith) d hd q hq hQ s hs hS) := by
  rw [finiteLaw_pi_map]
  congr 1
  funext e
  cases e with
  | inl e=>exact expanded_ordinary_selected_physical_law p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum
  | inr e=>
    apply finiteLaw_ext
    intro z
    simp [FiniteLaw.map,expandedOrdinarySelectedCollapse,rawExpandedMarkedWheelLaw,rawWheelLaw]
end Oberwolfach
