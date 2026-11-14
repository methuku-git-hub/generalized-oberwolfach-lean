module

public import Oberwolfach.MarkedFiniteRemainderAbsorber

@[expose] public section

/-! The simultaneous conclusion for every later bounded divisible
remainder in one fixed marked host, with explicit size and avoidance
conditions. This is a property to be proved, not an additional axiom. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U]
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

def MarkedFiniteAbsorberProperty (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop)
    (π:Equiv.Perm V) (b l:ℕ) (ε:ℝ) (s a₀ b₀ f:ℕ):Prop:=
    ∀ (A:Finset (E⊕K)) (S:Finset (V×U)),MarkedRemainderDivisible tail head ktail khead HK A S (l+4)→
    (markedRemainderRows tail head ktail khead A S).card+(markedRemainderHubs S).card≤s→
    (∀ z∈S,H₀ z.1 z.2∨HK z.1 z.2)→
    ∀ (W:Finset V) (B:Finset U) (F₀:Finset (Finset V⊕(V×U))),
    F₀.card≤f→(∀ e:Finset V,Sum.inl e∈F₀→e.card≤2)→markedRemainderHubs S⊆B→
    (B.card:ℝ)≤ε*Fintype.card V+f→(W.card:ℝ)≤ε*Fintype.card V+f→
    ∃ C:MarkedSupportedEdgeSet tail head ktail khead π U,
      IsResourceAbsorber (fun D:MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources D)
        (A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr) C.edges∧
      Disjoint C.edges F₀∧C.rows.card≤a₀∧C.hubs.card≤b₀∧
      (∀ v∈C.rows,v∈W∪markedRemainderRows tail head ktail khead A S→v∈markedRemainderRows tail head ktail khead A S)∧
      (∀ u∈C.hubs,u∈B→u∈markedRemainderHubs S)∧
      (∀ e∈C.edges,¬MarkedOldResource tail head ktail khead π (W∪markedRemainderRows tail head ktail khead A S) B e)∧
      (∀ v∈C.rows\markedRemainderRows tail head ktail khead A S,∀ w∈C.rows\markedRemainderRows tail head ktail khead A S,
        v≠w→¬PermutationClose π b v w)∧
      ∀ v∈C.rows\markedRemainderRows tail head ktail khead A S,∀ w∈markedRemainderRows tail head ktail khead A S,
        ¬PermutationClose π b v w

end Oberwolfach
