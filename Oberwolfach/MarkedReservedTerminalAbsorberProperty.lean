module

public import Oberwolfach.MarkedUniversalTerminalAbsorberAvoidance

@[expose] public section

/-! A fixed terminal reservoir, chosen before its later divisible
remainder, with explicit row, hub, edge and forbidden-resource bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U]
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

def MarkedReservedTerminalAbsorberProperty
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V)
    (b l s a₀ b₀ e₀ f:ℕ) (ε:ℝ):Prop:=
    ∀ (X:Finset V) (Z:Finset U),X.card+Z.card≤s→
    ∀ (W:Finset V) (B:Finset U),X⊆W→Z⊆B→
    (W.card:ℝ)≤ε*Fintype.card V+f→(B.card:ℝ)≤ε*Fintype.card V+f→
    ∀ F₀:Finset (Finset V⊕(V×U)),F₀.card≤f→
    ∀ (A₀:Finset (E⊕K)) (S₀:Finset (V×U)),
    markedRemainderRows tail head ktail khead A₀ S₀⊆X→markedRemainderHubs S₀⊆Z→
    (∀ z∈S₀,H₀ z.1 z.2∨HK z.1 z.2)→
    ∃ C:MarkedSupportedEdgeSet tail head ktail khead π U,
      Disjoint C.edges F₀∧C.edges.card≤e₀∧C.rows.card≤a₀∧C.hubs.card≤b₀∧
      (∀ e∈C.edges,¬MarkedOldResource tail head ktail khead π W B e)∧
      HasResourceDecomposition
        (fun W:MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources W) C.edges∧
      ∀ A⊆A₀,∀ S⊆S₀,MarkedRemainderDivisible tail head ktail khead HK A S (l+4)→
        IsResourceAbsorber
          (fun W:MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources W)
          (A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr) C.edges

theorem marked_finite_to_reserved_terminal_absorber
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (b l s a₀ b₀ f:ℕ) (ε:ℝ)
    (habs:MarkedFiniteAbsorberProperty tail head ktail khead H₀ HK π b l ε s a₀ b₀
      (f+2^(2*s^2)*(2*a₀^2+a₀*b₀))):
    MarkedReservedTerminalAbsorberProperty tail head ktail khead H₀ HK π b l s
      (2^(2*s^2)*a₀) (2^(2*s^2)*b₀) (2^(2*s^2)*(2*a₀^2+a₀*b₀)) f ε := by
  intro X Z hs W B hXW hZB hW hB F₀ hF A₀ S₀ hr hu hsp
  have hff:(f:ℝ)≤(f+2^(2*s^2)*(2*a₀^2+a₀*b₀):ℕ):=by
    exact_mod_cast Nat.le_add_right f (2^(2*s^2)*(2*a₀^2+a₀*b₀))
  apply marked_universal_terminal_absorber_avoiding tail head ktail khead π H₀ HK hp
    b l s a₀ b₀ (f+2^(2*s^2)*(2*a₀^2+a₀*b₀)) ε habs X Z F₀ W B hXW hZB
    (by linarith)
    (by linarith) hs
    (Nat.add_le_add_right hF _) A₀ S₀ hr hu hsp

end Oberwolfach
