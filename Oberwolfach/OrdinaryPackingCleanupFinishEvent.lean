module

public import Oberwolfach.OrdinaryTriangleFinishSampleInputs

@[expose] public section
/-! Add the triangle finish to a packing-and-cleanup event on the same
outcome, without altering its probability bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def OrdinaryPackingCleanupOutcome (Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (σ:Sym2 (V⊕U)→Bool) (τ ν:ℝ):Prop:=
  let R:=retainedGraph (ordinaryBoundaryGraph Q H X Z) σ;
  ∃M:OrdinaryUnreservedPackingData Q F H X Z R 3 (τ*Fintype.card (V⊕U)),
  let C:=ordinaryPackingUsedGraph Q F H X Z R 3 (τ*Fintype.card (V⊕U)) M;
  let Q₁:=ordinaryPackingPostRim Q F H X Z R 3 (τ*Fintype.card (V⊕U)) M;
  let H₁:=ordinaryPackingPostSpokes Q F H X Z R 3 (τ*Fintype.card (V⊕U)) M;
  Nonempty (OrdinaryOutsideCleanupData Q₁ F H₁ X Z C 3 (ν*Fintype.card (V⊕U)))

def OrdinaryPackingCleanupFinishOutcome (Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (σ:Sym2 (V⊕U)→Bool) (p τ ν:ℝ):Prop:=
  let R:=retainedGraph (ordinaryBoundaryGraph Q H X Z) σ;
  ∃M:OrdinaryUnreservedPackingData Q F H X Z R 3 (τ*Fintype.card (V⊕U)),
  let C:=ordinaryPackingUsedGraph Q F H X Z R 3 (τ*Fintype.card (V⊕U)) M;
  let Q₁:=ordinaryPackingPostRim Q F H X Z R 3 (τ*Fintype.card (V⊕U)) M;
  let H₁:=ordinaryPackingPostSpokes Q F H X Z R 3 (τ*Fintype.card (V⊕U)) M;
  ∃K:OrdinaryOutsideCleanupData Q₁ F H₁ X Z C 3 (ν*Fintype.card (V⊕U)),
    OrdinaryTriangleFinishResult
      (ordinaryCleanupPostRim Q₁ F H₁ X Z C 3 (ν*Fintype.card (V⊕U)) K)
      (ordinaryCleanupPostSpokes Q₁ F H₁ X Z C 3 (ν*Fintype.card (V⊕U)) K) X Z p

theorem ordinary_packing_cleanup_outcome_has_finish
    (Q₀ Q F:SimpleGraph V) (H₀ H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (σ:Sym2 (V⊕U)→Bool) (γ κ b B ε η ζ p εs τ ν:ℝ)
    (i:OrdinaryTriangleFinishSampleInputs Q₀ Q F H₀ H X Z σ γ κ b B ε η ζ p εs τ ν)
    (h:OrdinaryPackingCleanupOutcome Q₀ F H₀ X Z σ τ ν):
    OrdinaryPackingCleanupFinishOutcome Q₀ F H₀ X Z σ p τ ν:=by
  obtain ⟨M,⟨K⟩⟩:=h
  exact ⟨M,K,ordinary_triangle_finish_from_sample_inputs Q₀ Q F H₀ H X Z σ γ κ b B ε η ζ p εs τ ν i M K⟩

theorem ordinary_packing_cleanup_finish_event {Ω:Type} [Fintype Ω]
    (μ:FiniteLaw Ω) (E:Ω→Prop) (e:ℝ)
    (Q₀ Q F:Ω→SimpleGraph V) (H₀ H:Ω→V→U→Prop) (X:Ω→Finset V) (Z:Ω→Finset U)
    (σ:Ω→Sym2 (V⊕U)→Bool) (γ κ b B ε η ζ p εs τ ν:ℝ)
    (hprob:1-e≤μ.probability (fun a=>E a ∧ OrdinaryPackingCleanupOutcome (Q₀ a) (F a) (H₀ a) (X a) (Z a) (σ a) τ ν))
    (hinput:∀a,E a→OrdinaryTriangleFinishSampleInputs (Q₀ a) (Q a) (F a) (H₀ a) (H a) (X a) (Z a) (σ a)
      γ κ b B ε η ζ p εs τ ν):
    1-e≤μ.probability (fun a=>E a ∧ OrdinaryPackingCleanupFinishOutcome (Q₀ a) (F a) (H₀ a) (X a) (Z a) (σ a) p τ ν):=by
  apply hprob.trans
  apply finiteLaw_probability_mono
  intro a ha
  exact ⟨ha.1,ordinary_packing_cleanup_outcome_has_finish (Q₀ a) (Q a) (F a) (H₀ a) (H a)
    (X a) (Z a) (σ a) γ κ b B ε η ζ p εs τ ν (hinput a ha.1) ha.2⟩
end Oberwolfach
