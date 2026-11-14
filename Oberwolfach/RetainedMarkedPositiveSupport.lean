module

public import Oberwolfach.RawMarkedRetention
public import Oberwolfach.RetainedMarkedSpokeGeometry
public import Oberwolfach.MixedClassActualRetention

@[expose] public section
/-! Positive mass under the original joint law excludes a retained marked
spoke at a hub whose supplied marked density is zero. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [Nonempty V] [LinearOrder V] [DecidableEq U]

theorem retained_marked_spoke_positive_density
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d) (g₀:Γ)
    (p k:ℝ) (hp:0≤p) (hk:0≤k) (hphys:2*p+2*k≤1)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d g₀)
    (hpos:0<(rawMarkedRetentionLaw π d hd g₀ p k hp hk hphys q hq hQ s hs hS).mass z)
    (g:Γ) (j:Color) (v:V) (u:U)
    (hspoke:retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) g₀
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g₀)) z.2 g j true v u):
    0<q u g := by
  let σ : RawIntervalFamilyOutcome V U Γ Color:=fun e=>z.1 (Sum.inr e)
  let J := z.2
  have hstate : retainedIntervalState π d (fun e=>σ (u,e))
      (retainedRawStart π d σ g₀ _ J u) v=some (Sum.inl g) := hspoke
  have hc := (retainedIntervalState_interval_iff π d (fun e=>σ (u,e))
    (retainedRawStart π d σ g₀ _ J u) (fun a g h=>h.1) v g).mp hstate
  obtain ⟨a,ha,_⟩:=hc
  have hstart : z.1 (Sum.inr (u,Sum.inr (Sum.inl a)))=some g := ha.1.2
  by_contra hnot
  have hz:q u g=0:=le_antisymm (le_of_not_gt hnot) (hq u g)
  have hzero :
      (rawMarkedWheelLaw p k hp hk hphys d hd q hq hQ s hs hS
        (Sum.inr (u,Sum.inr (Sum.inl a)))).mass
        (z.1 (Sum.inr (u,Sum.inr (Sum.inl a))))=0 := by
    rw [hstart]
    simp [rawMarkedWheelLaw,rawIntervalFamilyLaw,rawIntervalCoordinateLaw,
      rawIntervalStartLaw,FiniteLaw.withRemainder,hz]
  have hprod : (∏ e,(rawMarkedWheelLaw p k hp hk hphys d hd q hq hQ s hs hS e).mass (z.1 e))=0 :=
    Finset.prod_eq_zero (Finset.mem_univ _) hzero
  change 0<((∏ e,(rawMarkedWheelLaw p k hp hk hphys d hd q hq hQ s hs hS e).mass (z.1 e))*_) at hpos
  rw [hprod,zero_mul] at hpos
  exact (lt_irrefl (0:ℝ)) hpos
/-- The same positivity conclusion holds under the expanded physical law
and its original conditional retention, on the very same outcome. -/
theorem expanded_retained_marked_spoke_positive_density
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d) (g₀:Bool)
    (p k p₂ k₂ u₀:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu₀:0≤u₀)
    (hsum:2*p+2*k+2*p₂+2*k₂+u₀≤1)
    (q:U→Bool→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Bool→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (z:Σ ω:MixedClassRaw (V:=V) (U:=U) true,mixedClassRetentionSpace true π d g₀ ω)
    (hpos:0<((FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V)
      p k p₂ k₂ u₀ hp hk hp₂ hk₂ hu₀ hsum d hd q hq hQ s hs hS)).sigma
        (mixedClassActualRetention true π d g₀)).mass z)
    (g j:Bool) (v:V) (u:U)
    (hspoke:retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) g₀
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g₀)) z.2 g j true v u):
    0<q u g := by
  let σ : RawIntervalFamilyOutcome V U Bool Bool:=fun e=>z.1 (Sum.inr e)
  let J := z.2
  have hstate : retainedIntervalState π d (fun e=>σ (u,e))
      (retainedRawStart π d σ g₀ _ J u) v=some (Sum.inl g) := hspoke
  have hc := (retainedIntervalState_interval_iff π d (fun e=>σ (u,e))
    (retainedRawStart π d σ g₀ _ J u) (fun a g h=>h.1) v g).mp hstate
  obtain ⟨a,ha,_⟩:=hc
  have hstart : z.1 (Sum.inr (u,Sum.inr (Sum.inl a)))=some g := ha.1.2
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
