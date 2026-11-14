module

public import Oberwolfach.OrdinaryCoveredRemainderTwoHosts
public import Oberwolfach.ReindexedResourceIteration

@[expose] public section
/-! A checked ordinary level-step invariant and a protected terminal
reservoir complete the original wheel host on the same resource universe. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_level_chain_reservoir_completion_two_hosts
    (Q P Ref F:SimpleGraph V) (H Hbase Href:V→U→Prop) (r m:ℕ)
    (hRefP:Ref≤P) (hHref:∀v u,Href v u→Hbase v u)
    (W:Finset V) (B:Finset U) (hsize:W.card+B.card≤m)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card)
    (hP:∀v∈W,∀w∈W,Q.Adj v w→Ref.Adj v w)
    (hH:∀v∈W,∀u∈B,H v u→Href v u)
    (A:Finset (Sym2 V⊕(V×U))) (hA:A⊆ordinaryHostResources Q H)
    (hdecA:HasResourceDecomposition (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=r)) A)
    (hres:∀(G':SimpleGraph V) (H':V→U→Prop),
      ordinaryHostResources G' H'⊆ordinaryRootResources W B →
      (ordinaryPhysicalGraph G' H').support.toFinset.card≤m →
      (∀v,G'.degree v=2*(Finset.univ.filter (H' v)).card) →
      (∀u,r∣(Finset.univ.filter (fun v=>H' v u)).card) →
      G'≤Ref → (∀v u,H' v u→Href v u) →
      IsResourceAbsorber (ordinaryWheelResources (P:=Ref) (F:=F) (Hbase:=Href) (r:=r))
        (ordinaryHostResources G' H') A)
    (L:ℕ) (Good:ℕ→Finset (Sym2 V⊕(V×U))→Prop)
    (hInitial:Good 0 (ordinaryHostResources Q H\A))
    (hStep:∀i<L,∀S,Good i S→∃T,Good (i+1) T ∧ T⊆S ∧
      HasResourceDecomposition (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=r)) (S\T))
    (hTerminal:∀T,Good L T→T⊆ordinaryRootResources W B):
    HasOrdinaryWheelDecomposition Q H r:=by
  let Host:=ordinaryHostResources Q H
  let Wheel:=ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=r)
  let State:=fun _:ℕ=>Finset (Sym2 V⊕(V×U))
  let contents:=fun (_:ℕ) (S:Finset (Sym2 V⊕(V×U)))=>S
  obtain ⟨T,hT,hsub,hdec⟩:=reindexed_resource_iteration Wheel State contents Good L hStep (Host\A) hInitial
  let D:Finset (Sym2 V⊕(V×U)):=(Host\A)\T
  have hD:D⊆Host:=Finset.sdiff_subset.trans Finset.sdiff_subset
  have hdis:Disjoint A D:=by
    apply Finset.disjoint_left.mpr
    intro e he hD'
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hD').1).2 he
  have hroot:Host\(A∪D)⊆ordinaryRootResources W B:=by
    have heq:Host\(A∪D)=T:=by
      ext e
      have ht:e∈T→e∈Host ∧ e∉A:=by
        intro he
        exact Finset.mem_sdiff.mp (hsub he)
      simp only [D,Finset.mem_sdiff,Finset.mem_union]
      tauto
    rw [heq]
    exact hTerminal T hT
  exact ordinary_covered_remainder_completion_two_hosts Q P Ref F H Hbase Href r m hRefP hHref W B hsize hbal hdiv hP hH
    A D hA hD hdis hdecA hdec hroot hres
end Oberwolfach
