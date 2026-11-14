module

public import Oberwolfach.MarkedFixedVortexGeometry
public import Oberwolfach.MarkedFiniteDomainBalanceBounds

@[expose] public section
/-! At the last parent level both deeper domains are empty, so every
ambient-root balance on these domains is exactly zero. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ}

theorem marked_vortex_terminal_deeper_balance_zero
    (Q:Vortex U G D β ε m) (L:ℕ) (hL:L+1=Q.length):
    let W:=markedVortexVertexType Q L
    let Z:=markedVortexHubType Q L;
    (markedVortexDeeperVertices Q L=∅) ∧ (markedVortexDeeperHubs Q L=∅) ∧
    ∀ (E K:Type) [DecidableEq E] [DecidableEq K]
      (tail head:E→W) (ktail khead:K→W) (HK:W→Z→Prop)
      (A:Finset (E⊕K)) (S:Finset (W×Z)) (c:ℕ) (z:W⊕Z) (i:Fin 4),
      markedFiniteDomainBalance tail head ktail khead HK A S c
        (markedVortexDeeperVertices Q L) (markedVortexDeeperHubs Q L) z i=0 := by
  intro W Z
  have hW:markedVortexDeeperVertices Q L=∅ := by
    unfold markedVortexDeeperVertices
    rw [Q.extendedVertices_empty (by omega)]
    simp
  have hZ:markedVortexDeeperHubs Q L=∅ := by
    unfold markedVortexDeeperHubs
    rw [Q.extendedIndices_empty (by omega)]
    simp
  refine ⟨hW,hZ,?_⟩
  intro E K _ _ tail head ktail khead HK A S c z i
  apply markedFiniteDomainBalance_zero_of_avoids tail head ktail khead HK A S c _ _ _ _ z i
  · intro a ha
    simp [hW]
  · intro s hs
    simp [hW,hZ]
end Oberwolfach
