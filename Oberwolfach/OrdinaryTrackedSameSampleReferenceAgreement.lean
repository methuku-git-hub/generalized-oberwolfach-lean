module

public import Oberwolfach.OrdinaryTrackedComplementWitness
public import Oberwolfach.OrdinaryCorrectedReservoirNamedWitness

@[expose] public section
/-! The tracked complement and the corrected reservoir provide the three
reference-agreement hypotheses needed at every later level on the same sample. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_tracked_same_sample_reference_agreement {n q r mAbs t aAbs bAbs:ℕ}
    (P S:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Fs:Fin q→SimpleGraph (Fin n)) (C:∀u,Finset (Fs u).ConnectedComponent)
    (Inner Z Wterm:Finset (Fin n)) (Hubs Bterm:Finset (Fin q)) (ξ:ℝ)
    (K:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))) (JQ:SimpleGraph (Fin n)) (JH:Fin n→Fin q→Prop)
    (cost:ℝ) (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n):
    let raw:=fun e=>expandedOrdinarySelectedCollapse e (σ e)
    let Bad:=permutationConflictGraph π (3*d)
    let R:=rawWheelGraph P raw
    let J:=rawWheelSpokes π d raw false
    let Gbase:=S\ordinaryEmbeddedComplements Fs C f
    let Hbase:=fun v u=>v∉Set.range (f u);
    OrdinaryCorrectedProtectedReservoirWitness r mAbs t aAbs bAbs ξ (R\Bad) Bad J Z Inner Wterm Bterm Hubs K JQ JH→
    OrdinaryTrackedComplementFor P S π d σ Fs C Inner Hubs K cost f→
    (∀v∈Inner,∀w∈Inner,(R\Bad).Adj v w↔Gbase.Adj v w) ∧
    (∀v∈Inner,∀u∈Hubs,J v u↔Hbase v u) ∧
    Disjoint K (ordinaryRootResources Inner Hubs) :=by
  intro raw Bad R J Gbase Hbase hw hf
  have hf':=hf
  unfold OrdinaryTrackedComplementFor at hf'
  obtain ⟨_,_,_,hrim,hspoke,_,_⟩:=hf'
  refine ⟨?_,?_,hw.2.1⟩
  · intro v hv w hw
    exact (hrim v hv w hw).symm
  · intro v hv u hu
    exact (hspoke v hv u hu).symm
end Oberwolfach
