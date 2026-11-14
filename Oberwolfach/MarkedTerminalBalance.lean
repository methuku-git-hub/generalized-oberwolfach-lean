module

public import Oberwolfach.MarkedFiniteDomainBalance
public import Oberwolfach.MarkedFixedVortexGeometry

@[expose] public section
/-! Balance on the appended empty terminal vortex pair. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_finite_domain_balance_empty
    {V U E K:Type} [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]
    (tail head:E→V) (ktail khead:K→V) (HK:V→U→Prop)
    (A:Finset (E⊕K)) (S:Finset (V×U)) (m:ℕ) (z:V⊕U) (j:Fin 4):
    markedFiniteDomainBalance tail head ktail khead HK A S m ∅ ∅ z j=0:=by
  cases z <;> fin_cases j <;> simp [markedFiniteDomainBalance,markedFiniteBalance]

theorem marked_vortex_deeper_terminal_empty
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)
    (i:ℕ) (hi:Q.length < i + 2):
    markedVortexDeeperVertices Q i=∅ ∧ markedVortexDeeperHubs Q i=∅:=by
  constructor
  · ext x
    simp [markedVortexDeeperVertices,Q.extendedVertices_empty hi]
  · ext u
    simp [markedVortexDeeperHubs,Q.extendedIndices_empty hi]
theorem marked_vortex_terminal_balance_zero
    {V U E K:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U] [DecidableEq E] [DecidableEq K]
    {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)
    (i:ℕ) (hi:Q.length < i + 2)
    (tail head:E→markedVortexVertexType Q i) (ktail khead:K→markedVortexVertexType Q i)
    (HK:markedVortexVertexType Q i→markedVortexHubType Q i→Prop)
    (A:Finset (E⊕K)) (S:Finset (markedVortexVertexType Q i×markedVortexHubType Q i))
    (n:ℕ) (z:markedVortexVertexType Q i⊕markedVortexHubType Q i) (j:Fin 4):
    markedFiniteDomainBalance tail head ktail khead HK A S n
      (markedVortexDeeperVertices Q i) (markedVortexDeeperHubs Q i) z j=0:=by
  obtain ⟨hv,hu⟩:=marked_vortex_deeper_terminal_empty Q i hi
  rw [hv,hu]
  exact marked_finite_domain_balance_empty tail head ktail khead HK A S n z j
/-- Deleting resources cannot change balance on the appended empty pair. -/
theorem marked_vortex_terminal_balance_invariant
    {V U E K E' K':Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    [DecidableEq E] [DecidableEq K] [DecidableEq E'] [DecidableEq K']
    {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)
    (i:ℕ) (hi:Q.length < i + 2)
    (tail head:E→markedVortexVertexType Q i) (ktail khead:K→markedVortexVertexType Q i)
    (tail' head':E'→markedVortexVertexType Q i) (ktail' khead':K'→markedVortexVertexType Q i)
    (HK HK':markedVortexVertexType Q i→markedVortexHubType Q i→Prop)
    (A:Finset (E⊕K)) (S:Finset (markedVortexVertexType Q i×markedVortexHubType Q i))
    (A':Finset (E'⊕K')) (S':Finset (markedVortexVertexType Q i×markedVortexHubType Q i))
    (n:ℕ) (z:markedVortexVertexType Q i⊕markedVortexHubType Q i) (j:Fin 4):
    markedFiniteDomainBalance tail head ktail khead HK A S n
      (markedVortexDeeperVertices Q i) (markedVortexDeeperHubs Q i) z j =
    markedFiniteDomainBalance tail' head' ktail' khead' HK' A' S' n
      (markedVortexDeeperVertices Q i) (markedVortexDeeperHubs Q i) z j :=by
  rw [marked_vortex_terminal_balance_zero Q i hi tail head ktail khead HK A S n z j,
      marked_vortex_terminal_balance_zero Q i hi tail' head' ktail' khead' HK' A' S' n z j]
end Oberwolfach
