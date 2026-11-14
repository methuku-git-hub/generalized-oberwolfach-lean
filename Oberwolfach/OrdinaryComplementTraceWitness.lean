module

public import Oberwolfach.OrdinaryWheelTraceWitness
public import Oberwolfach.OrdinaryComplementRemainderBalance
public import Oberwolfach.OrdinaryComplementRemainderDecomposition

@[expose] public section
/-! A protected wheel trace completes the actual complement remainder,
    with balance and divisibility derived from the embedded factors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_complement_trace_witness_completion {n q r:ℕ}
    (S P Fbad:SimpleGraph (Fin n)) (hS:S.IsRegularOfDegree (2*q)) (hr:0<r)
    (Fs:Fin q→SimpleGraph (Fin n)) (hF:∀u,(Fs u).IsRegularOfDegree 2)
    (C:∀u,Finset (Fs u).ConnectedComponent) (hComponent:∀u (c:↥(C u)),Fintype.card c.val=r)
    (fC:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (hC:∀u x y,((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).Adj x y→S.Adj (fC u x) (fC u y))
    (hCC:∀u v,u≠v→Disjoint
      (partialFactorPhysicalEdgesPoly {x:Fin n // (Fs u).connectedComponentMk x∉C u}
        ((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}) (fC u))
      (partialFactorPhysicalEdgesPoly {x:Fin n // (Fs v).connectedComponentMk x∉C v}
        ((Fs v).induce {x | (Fs v).connectedComponentMk x∉C v}) (fC v)))
    (Hbase:Fin n→Fin q→Prop)
    (hTrace:OrdinaryWheelTraceWitness (S\ordinaryEmbeddedComplements Fs C fC) P Fbad
      (fun v u=>v∉Set.range (fC u)) Hbase r):
    HasOrdinaryWheelDecomposition (S\ordinaryEmbeddedComplements Fs C fC) (fun v u=>v∉Set.range (fC u)) r ∧
    HasFactorDecomposition S Fs :=by
  obtain ⟨hbal,hdiv⟩:=ordinary_complement_remainder_balance S hS Fs hF C hComponent fC hC hCC
  have hWheel:=ordinary_wheel_trace_witness_completion (S\ordinaryEmbeddedComplements Fs C fC) P Fbad
    (fun v u=>v∉Set.range (fC u)) Hbase r
    (by intro v; have hh:=hbal v; convert hh using 1 <;> congr 6 <;> first | rfl | exact Subsingleton.elim _ _)
    (by intro u; have hh:=hdiv u; convert hh using 1 <;> congr 6 <;> first | rfl | exact Subsingleton.elim _ _)
    hTrace
  exact ⟨hWheel,ordinary_complement_remainder_decomposition S hS hr Fs hF C hComponent fC hC hCC hWheel⟩
end Oberwolfach
