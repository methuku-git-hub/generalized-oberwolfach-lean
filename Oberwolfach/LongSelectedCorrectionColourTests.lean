module

public import Oberwolfach.LongUnassignedDensityBounds
public import Oberwolfach.LongAllStructuralSelectorConcreteBoundaryEvent

@[expose] public section
/-! The colour and start tests on the selected expanded sample yield the
orientation and unassigned-degree inputs of the first-vortex correction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance selectedCorrectionColourFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem long_selected_correction_colour_tests
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r D:ℕ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (θ:ℝ) (hK:0<K) (hD:0<D) (hθ:0≤θ) (hθ1:θ≤1)
    (hρ:initialIndexDensity U D≤1)
    (z:MarkedExpandedActualOutcome (U:=U) π d)
    (p₂ k₂:ℝ):
    let p₁:=initialIndexDensity U D*(1/100:ℝ)/2
    let k₁:=initialIndexDensity U D*((1/100:ℝ)/((r+4:ℕ):ℝ))/2
    let u:=2*(∑w:U,(1-(1/100:ℝ)-(1/100:ℝ)/((r+4):ℝ)-
      longAssignedApproxMarkedWeight F hF K (r+4) θ w-longAssignedApproxOrdinaryWeight F hF K (r+4) θ w))/(D:ℝ);
    (∀j x,
      |((∑y,sampledColourOrientation P (fun e=>z.1 (Sum.inl e)) j x y:ℕ):ℝ)-markedExpandedPhysicalProbability p₁ k₁ p₂ k₂ u j/2*P.degree x|<(n:ℝ)^(3/5:ℝ) ∧
      |((∑y,sampledColourOrientation P (fun e=>z.1 (Sum.inl e)) j y x:ℕ):ℝ)-markedExpandedPhysicalProbability p₁ k₁ p₂ k₂ u j/2*P.degree x|<(n:ℝ)^(3/5:ℝ) ∧
      |(sampledColourDegree P (fun e=>(z.1 (Sum.inl e)).1) j x:ℝ)-markedExpandedPhysicalProbability p₁ k₁ p₂ k₂ u j*P.degree x|<(n:ℝ)^(3/5:ℝ))→
    (∀g x,|((rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g x).card:ℝ)-
      (∑w,longAssignedIntervalProbability F hF K (r+4) θ w g/(d:ℝ))|<(n:ℝ)^(3/5:ℝ))→
    0≤u ∧ u≤2*θ ∧
    (∀v,|((rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false v).card:ℝ)-
      (∑w,longAssignedIntervalProbability F hF K (r+4) θ w false/(d:ℝ))|<(n:ℝ)^(3/5:ℝ)) ∧
    (∀j v,|((∑x,sampledColourOrientation P (fun e=>z.1 (Sum.inl e)) j x v:ℕ):ℝ)-
      markedExpandedPhysicalProbability p₁ k₁ p₂ k₂ u j/2*P.degree v|<(n:ℝ)^(3/5:ℝ)) ∧
    (∀v,|((sampledColourDegree P (fun e=>(z.1 (Sum.inl e)).1) 4 v):ℝ)-u*(P.degree v:ℝ)|≤(n:ℝ)^(3/5:ℝ)) :=by
  intro p₁ k₁ u hColour hStart
  have hn:0<n:=by obtain ⟨x⟩:=‹Nonempty (Fin n)›; exact Fin.pos x
  obtain ⟨hu0,hu⟩:=long_unassigned_density_bounds hn hK (show 0<r+4 by omega) hD F hF θ hθ hθ1 hρ
  simp only [Nat.cast_add,Nat.cast_ofNat] at hu0 hu
  refine ⟨hu0,hu,fun v=>hStart false v,fun j v=>(hColour j v).2.1,?_⟩
  intro v
  have hv:=(hColour 4 v).2.2
  simpa [markedExpandedPhysicalProbability] using hv.le
end Oberwolfach
