module

public import Oberwolfach.IndexedMarkedComparison
public import Oberwolfach.IndexedMarkedExpansionSimplicity

@[expose] public section

/-! The common central expansion is formed only after retaining all typed
occurrences. It is balanced and has no loops or repeated directed arcs,
even though its pre-expansion row set is a singleton. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U A S:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V] [DecidableEq U] [DecidableEq A] [DecidableEq S]

def indexedMarkedCentralExpansion (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m):
    IndexedMarkedGraph (Unit⊕((A⊕S)×Fin (m+1))) (Unit⊕(A⊕S))
      (A⊕((A⊕S)×Fin (m+1))) (S⊕((A⊕S)×Fin (m+1))):=
  indexedMarkedExpansion (G.map (fun _=>()) (fun _=>())) m hm

theorem indexedMarkedCentralExpansion_balanced (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m)
    (hG:G.IsBalanced m):(indexedMarkedCentralExpansion G m hm).IsBalanced m:=
  indexedMarkedExpansion_balanced _ m hm (G.map_balanced m hG _ _)

theorem indexedMarkedExpansion_to_central (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m):
    (indexedMarkedExpansion G m hm).map (Sum.map (fun _=>()) id) (Sum.map (fun _=>()) id)=
      indexedMarkedCentralExpansion G m hm:=indexedMarkedExpansion_map G m hm _ _

theorem indexedMarkedComparisonExpansion_to_central (G:IndexedMarkedGraph V U A S)
    (m:ℕ) (hm:2≤m) (hG:G.IsBalanced m):
    (indexedMarkedExpansion (indexedMarkedComparison G m hG) m hm).map
      (Sum.map (fun _=>()) id) (Sum.map (fun _=>()) id)=indexedMarkedCentralExpansion G m hm:=by
  rw [indexedMarkedExpansion_map,indexedMarkedComparison_collapse]
  rfl

theorem indexedMarkedCentralExpansion_no_loops (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m):
    ∀ a,(indexedMarkedCentralExpansion G m hm).src a≠(indexedMarkedCentralExpansion G m hm).dst a:=
  indexedMarkedExpansion_no_loops _ m hm

theorem indexedMarkedCentralExpansion_rim_injective (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m):
    Function.Injective (fun a=>((indexedMarkedCentralExpansion G m hm).src a,
      (indexedMarkedCentralExpansion G m hm).dst a)):=indexedMarkedExpansion_rim_injective _ m hm

theorem indexedMarkedCentralExpansion_spoke_injective (G:IndexedMarkedGraph V U A S) (m:ℕ) (hm:2≤m):
    Function.Injective (fun s=>((indexedMarkedCentralExpansion G m hm).row s,
      (indexedMarkedCentralExpansion G m hm).hub s)):=indexedMarkedExpansion_spoke_injective _ m hm

end Oberwolfach
