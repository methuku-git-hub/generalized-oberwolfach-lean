module

public import Oberwolfach.OrdinaryPackingCleanupFinishEvent
public import Oberwolfach.OrdinaryTriangleCoverDownResult

@[expose] public section
/-! The three actual same-sample wheel packings form a one-level triangle
cover-down and a balanced divisible inner remainder. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
set_option synthInstance.maxSize 2048
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_cover_down_from_sample_outcome
    (Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U) (σ:Sym2 (V⊕U)→Bool) (p τ ν:ℝ)
    (h:OrdinaryPackingCleanupFinishOutcome Q F H X Z σ p τ ν):
    OrdinaryTriangleCoverDownResult Q H X Z:=by
  obtain ⟨M,K,hfinish⟩:=h
  let R:=retainedGraph (ordinaryBoundaryGraph Q H X Z) σ
  let A:=ordinaryWheelRimGraph M.wheels
  let S:=ordinaryPackingSpokes M.wheels
  let B:=wheelFamilyRim K.wheels
  let T:=wheelFamilySpokes K.wheels
  have hA:HasOrdinaryWheelDecomposition A S 3:=ordinaryPacking_decomposition M.wheels M.disjoint
  have hB:HasOrdinaryWheelDecomposition B T 3:=K.decomposition
  have hAsub:A≤Q:=(ordinaryWheelRimGraph_subhost M.wheels).trans (sdiff_le.trans sdiff_le)
  have hSsub:∀v u,S v u→H v u:=by
    intro v u hvu
    obtain ⟨W,hW,hu,hv⟩:=hvu
    rw [←hu]
    exact (W.property.1 v hv).1
  have hK:=wheelFamily_subhost K.wheels
  have hBsub:B≤Q\A:=hK.1
  have hTsub:∀v u,T v u→H v u∧¬S v u:=hK.2
  exact ordinary_triangle_cover_down_from_three Q A B H S T X Z p hA hB hAsub hSsub hBsub hTsub hfinish

theorem ordinary_triangle_cover_down_same_sample {Ω:Type} [Fintype Ω]
    (μ:FiniteLaw Ω) (E:Ω→Prop) (e:ℝ)
    (Q F:Ω→SimpleGraph V) (H:Ω→V→U→Prop) (X:Ω→Finset V) (Z:Ω→Finset U)
    (σ:Ω→Sym2 (V⊕U)→Bool) (p τ ν:ℝ)
    (hprob:1-e≤μ.probability (fun a=>E a∧OrdinaryPackingCleanupFinishOutcome (Q a) (F a) (H a) (X a) (Z a) (σ a) p τ ν)):
    1-e≤μ.probability (fun a=>E a∧OrdinaryTriangleCoverDownResult (Q a) (H a) (X a) (Z a)):=by
  apply hprob.trans
  apply finiteLaw_probability_mono
  intro a ha
  exact ⟨ha.1,ordinary_triangle_cover_down_from_sample_outcome (Q a) (F a) (H a) (X a) (Z a) (σ a) p τ ν ha.2⟩
end Oberwolfach
