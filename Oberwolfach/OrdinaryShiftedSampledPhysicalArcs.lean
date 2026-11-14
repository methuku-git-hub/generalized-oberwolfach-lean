module

public import Oberwolfach.OrdinaryEligibleHost
public import Oberwolfach.RawMixedPhysicalArcHost

@[expose] public section
/-! Both typed rim representations in the ordinary construction refer to
ordinary sampled physical arcs; the eligible-host margin also supplies the
separation required after applying the permutation to a shifted endpoint. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]

theorem ordinary_shifted_sampled_physical_arcs
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (raw:RawMarkedOutcome V U Γ Color):
    let Q:=ordinaryEligibleHost P π d
    let R:=ordinaryShiftedPairRims Q π d raw;
    (∀e:{e:V×V // R (Sum.inl e)},Q.Adj e.val.1 e.val.2 ∧
      rawMixedPhysicalArc Q π d raw e.val.1 e.val.2) ∧
    (∀e:{e:V×V // R (Sum.inr e)},Q.Adj e.val.1 (π e.val.2) ∧
      rawMixedPhysicalArc Q π d raw e.val.1 (π e.val.2)) :=by
  intro Q R
  constructor
  · intro e
    have h:e.val.1≠e.val.2 ∧ Q.Adj e.val.1 e.val.2 ∧
        raw (Sum.inl s(e.val.1,e.val.2))=some (false,orientationBit e.val.1 e.val.2):=by
      have hh:e.val.1≠e.val.2:=(show Q.Adj e.val.1 e.val.2 from e.property.2.1).ne
      exact ⟨hh,e.property.2⟩
    refine ⟨h.2.1,Or.inl ?_⟩
    change markedPhysicalRim Q π (3*d) (fun e=>raw (Sum.inl e)) false e.val.1 e.val.2=1
    apply (markedPhysicalRim_eq_one_iff Q π (3*d) (fun e=>raw (Sum.inl e)) false _ _).2
    simpa [R,ordinaryShiftedPairRims] using e.property
  · intro e
    have hQ:Q.Adj e.val.1 (π e.val.2):=e.property.2.1
    refine ⟨hQ,Or.inl ?_⟩
    have hfar:¬PermutationClose π (3*d) e.val.1 (π e.val.2):=by
      intro hclose
      have hh:¬PermutationClose π (3*d+2) e.val.1 (π e.val.2):=(ordinary_eligible_host_adj P π d _ _).mp hQ |>.2
      exact hh (permutationClose_mono_radius π _ _ (by omega) _ _ hclose)
    change markedPhysicalRim Q π (3*d) (fun e=>raw (Sum.inl e)) false e.val.1 (π e.val.2)=1
    apply (markedPhysicalRim_eq_one_iff Q π (3*d) (fun e=>raw (Sum.inl e)) false _ _).2
    simpa using (show ¬PermutationClose π (3*d) e.val.1 (π e.val.2) ∧ Q.Adj e.val.1 (π e.val.2) ∧
      raw (Sum.inl s(e.val.1,π e.val.2))=some (false,orientationBit e.val.1 (π e.val.2)) from ⟨hfar,hQ,e.property.2.2⟩)
end Oberwolfach
