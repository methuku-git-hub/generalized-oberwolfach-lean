module

public import Oberwolfach.ExpandedRawMarkedPositiveSupport

@[expose] public section
/-! Positive mass under the original expanded law excludes raw marked
spokes at hubs with zero supplied density. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [Nonempty V] [LinearOrder V] [DecidableEq U]

theorem expanded_raw_marked_spoke_positive_density_any_stage
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (p k p₂ k₂ u₀:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu₀:0≤u₀)
    (hsum:2*p+2*k+2*p₂+2*k₂+u₀≤1)
    (q:U→Bool→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Bool→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
    [∀ω,Fintype (R ω)] (ν:∀ω,FiniteLaw (R ω))
    (z:Σ ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e,R ω)
    (hpos:0<((FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V)
      p k p₂ k₂ u₀ hp hk hp₂ hk₂ hu₀ hsum d hd q hq hQ s hs hS)).sigma
        ν).mass z)
    (g j:Bool) (v:V) (u:U)
    (hspoke:rawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) g j true v u):
    0<q u g := by
  let σ : RawIntervalFamilyOutcome V U Bool Bool:=fun e=>z.1 (Sum.inr e)
  have hstate : rawIntervalState π d (fun e=>σ (u,e)) v=some (Sum.inl g) := hspoke
  have hc := (rawIntervalState_interval_iff π d (fun e=>σ (u,e)) v g).mp hstate
  obtain ⟨a,ha,_⟩:=hc
  have hstart : z.1 (Sum.inr (u,Sum.inr (Sum.inl a)))=some g := ha.2
  by_contra hnot
  have hz:q u g=0:=le_antisymm (le_of_not_gt hnot) (hq u g)
  have hzero :
      (rawExpandedMarkedWheelLaw p k p₂ k₂ u₀ hp hk hp₂ hk₂ hu₀ hsum d hd q hq hQ s hs hS
        (Sum.inr (u,Sum.inr (Sum.inl a)))).mass
        (z.1 (Sum.inr (u,Sum.inr (Sum.inl a))))=0 := by
    rw [hstart]
    simp [rawExpandedMarkedWheelLaw,rawIntervalFamilyLaw,rawIntervalCoordinateLaw,
      rawIntervalStartLaw,FiniteLaw.withRemainder,hz]
  have hprod : (∏ e,(rawExpandedMarkedWheelLaw p k p₂ k₂ u₀ hp hk hp₂ hk₂ hu₀ hsum d hd q hq hQ s hs hS e).mass (z.1 e))=0 :=
    Finset.prod_eq_zero (Finset.mem_univ _) hzero
  change 0<((∏ e,(rawExpandedMarkedWheelLaw p k p₂ k₂ u₀ hp hk hp₂ hk₂ hu₀ hsum d hd q hq hQ s hs hS e).mass (z.1 e))*_) at hpos
  rw [hprod,zero_mul] at hpos
  exact (lt_irrefl (0:ℝ)) hpos
end Oberwolfach
