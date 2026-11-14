module

public import Oberwolfach.OrdinaryProtectedRequiredEdges

@[expose] public section
/-! Old sampled factor edges avoid the required graph when the earlier
matching avoids the corresponding sampled deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem ordinary_old_edges_avoid_protected_required
    (Target Sample Reference Protect Host:SimpleGraph V) (Inner:Finset V)
    (hRef:Reference≤Sample) (hProtect:Protect≤Reference)
    (Old:Finset (Sym2 V))
    (hSample:Old⊆Sample.edgeFinset)
    (hSurvive:Old⊆(Host\ordinaryProtectedSampleDeletion Sample Target Reference Protect Inner).edgeFinset):
    Disjoint Old (ordinaryProtectedRequired Target Sample Reference Inner).edgeFinset:=by
  apply Finset.disjoint_left.mpr
  intro e heOld heReq
  induction e using Sym2.inductionOn with
  | _ v w=>
    have hs:Sample.Adj v w:=SimpleGraph.mem_edgeFinset.mp (hSample heOld)
    have hd:(Host\ordinaryProtectedSampleDeletion Sample Target Reference Protect Inner).Adj v w:=
      SimpleGraph.mem_edgeFinset.mp (hSurvive heOld)
    have hr:(ordinaryProtectedRequired Target Sample Reference Inner).Adj v w:=SimpleGraph.mem_edgeFinset.mp heReq
    have hh:=ordinary_protected_required_edges_relations Target Sample Reference Protect Inner hRef hProtect
    exact hh.2.2.2 v w hr ⟨hs,hd.2⟩
end Oberwolfach
