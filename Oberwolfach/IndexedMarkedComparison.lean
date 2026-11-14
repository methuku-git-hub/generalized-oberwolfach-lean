module

public import Oberwolfach.IndexedMarkedWheelUnion
public import Oberwolfach.IndexedMarkedGraphCounts
public import Oberwolfach.TypedOccurrenceEquivalence

@[expose] public section

/-! Construct the disjoint-wheel comparison graph with exactly the original
rim and spoke index types. Its four typed counts are consequences of local
balance, not extra assumptions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U A S:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V] [DecidableEq U] [DecidableEq A] [DecidableEq S]

abbrev IndexedMarkedGraph.MarkedSpokes (G:IndexedMarkedGraph V U A S):Type:=
  {s:S // G.js s=true}

theorem indexedMarkedComparison_type_counts (G:IndexedMarkedGraph V U A S) (m:ℕ)
    (hG:G.IsBalanced m):
    (∀ t,Fintype.card {a:A // G.jr a=t}=
      Fintype.card {a:Empty⊕(G.MarkedSpokes×Fin (m+1)) // (indexedMarkedWheelUnion G.MarkedSpokes m).jr a=t})∧
    (∀ t,Fintype.card {s:S // G.js s=t}=
      Fintype.card {s:Empty⊕(G.MarkedSpokes×Fin (m+1)) // (indexedMarkedWheelUnion G.MarkedSpokes m).js s=t}):=by
  let J:=indexedMarkedWheelUnion G.MarkedSpokes m
  have hJ:=indexedMarkedWheelUnion_balanced (I:=G.MarkedSpokes) m
  have hI:=indexedMarkedWheelUnion_marked_spoke_count (I:=G.MarkedSpokes) m
  change Fintype.card {s // J.js s=true}=Fintype.card G.MarkedSpokes at hI
  constructor
  · intro t;cases t
    · exact (G.ordinary_rim_card m hG).trans ((congrArg (fun n=>m*n) hI.symm).trans (J.ordinary_rim_card m hJ).symm)
    · exact (G.marked_card m hG).trans (hI.symm.trans (J.marked_card m hJ).symm)
  · intro t;cases t
    · exact (G.ordinary_spoke_card m hG).trans ((congrArg (fun n=>m*n) hI.symm).trans (J.ordinary_spoke_card m hJ).symm)
    · exact hI.symm

def indexedMarkedComparison (G:IndexedMarkedGraph V U A S) (m:ℕ) (hG:G.IsBalanced m):
    IndexedMarkedGraph (G.MarkedSpokes×Fin (m+1)) G.MarkedSpokes A S:=
  (indexedMarkedWheelUnion G.MarkedSpokes m).pullbackOccurrences
    (typedOccurrenceEquiv G.jr (indexedMarkedWheelUnion G.MarkedSpokes m).jr (indexedMarkedComparison_type_counts G m hG).1)
    (typedOccurrenceEquiv G.js (indexedMarkedWheelUnion G.MarkedSpokes m).js (indexedMarkedComparison_type_counts G m hG).2)

theorem indexedMarkedComparison_balanced (G:IndexedMarkedGraph V U A S) (m:ℕ) (hG:G.IsBalanced m):
    (indexedMarkedComparison G m hG).IsBalanced m:=
  IndexedMarkedGraph.pullbackOccurrences_balanced _ m (indexedMarkedWheelUnion_balanced m) _ _

theorem indexedMarkedComparison_rim_type (G:IndexedMarkedGraph V U A S) (m:ℕ) (hG:G.IsBalanced m) (a:A):
    (indexedMarkedComparison G m hG).jr a=G.jr a:=typedOccurrenceEquiv_type _ _ _ _

theorem indexedMarkedComparison_spoke_type (G:IndexedMarkedGraph V U A S) (m:ℕ) (hG:G.IsBalanced m) (s:S):
    (indexedMarkedComparison G m hG).js s=G.js s:=typedOccurrenceEquiv_type _ _ _ _

theorem indexedMarkedComparison_collapse (G:IndexedMarkedGraph V U A S) (m:ℕ) (hG:G.IsBalanced m):
    (indexedMarkedComparison G m hG).map (fun _=>()) (fun _=>())=G.map (fun _=>()) (fun _=>()):=by
  apply indexedMarkedGraph_ext
  · rfl
  · rfl
  · rfl
  · rfl
  · funext a;exact indexedMarkedComparison_rim_type G m hG a
  · funext s;exact indexedMarkedComparison_spoke_type G m hG s

end Oberwolfach
