module

public import Oberwolfach.OrdinaryCorrectedReservoirSpokeLabels

@[expose] public section
/-! The row and column bounds hold for the already chosen reservoir witness;
no choice is made after the target graph is edited. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fixed_corrected_reservoir_spoke_labels
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e)
    (r m t a b:ℕ) (ξ:ℝ) (Q F:SimpleGraph V)
    (A Z Wterm:Finset V) (Bterm B:Finset U)
    (K:Finset (Sym2 V⊕(V×U))) (JQ:SimpleGraph V) (JH:V→U→Prop)
    (hW:OrdinaryCorrectedProtectedReservoirWitness r m t a b ξ Q F
      (rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false) A Z Wterm Bterm B K JQ JH):
    (∀u,ordinaryReservoirSpokeLabels K u⊆rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u) ∧
    (∀u,(ordinaryReservoirSpokeLabels K u).card≤2^(t*t)*a) ∧
    (∀v,(Finset.univ.filter (fun u=>v∈ordinaryReservoirSpokeLabels K u)).card≤2^(t*t)*b) :=by
  obtain ⟨hsub,hrow,hcol⟩:=ordinary_reservoir_spoke_labels_inputs π d σ Q K hW.1
  refine ⟨hsub,?_,?_⟩
  · intro u;exact (hrow u).trans hW.2.2.1
  · intro v;exact (hcol v).trans hW.2.2.2.1
end Oberwolfach
