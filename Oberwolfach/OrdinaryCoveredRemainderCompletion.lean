module

public import Oberwolfach.OrdinaryTerminalRemainderBalance
public import Oberwolfach.OrdinaryRootTerminalGeometry

@[expose] public section
/-! A wheel packing that leaves only terminal-root resources can be joined
to a universal reservoir. Balance, divisibility, and the terminal order are
proved for the actual leftover, rather than assumed independently. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_covered_remainder_completion
    (Q P F:SimpleGraph V) (H Hbase:V→U→Prop) (r m:ℕ)
    (W:Finset V) (B:Finset U) (hsize:W.card+B.card≤m)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card)
    (hP:∀v∈W,∀w∈W,Q.Adj v w→P.Adj v w)
    (hH:∀v∈W,∀u∈B,H v u→Hbase v u)
    (A D:Finset (Sym2 V⊕(V×U)))
    (hA:A⊆ordinaryHostResources Q H) (hD:D⊆ordinaryHostResources Q H)
    (hdis:Disjoint A D)
    (hdecA:HasResourceDecomposition (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=r)) A)
    (hdecD:HasResourceDecomposition (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=r)) D)
    (hroot:ordinaryHostResources Q H\(A∪D)⊆ordinaryRootResources W B)
    (hres:∀(G':SimpleGraph V) (H':V→U→Prop),
      ordinaryHostResources G' H'⊆ordinaryRootResources W B →
      (ordinaryPhysicalGraph G' H').support.toFinset.card≤m →
      (∀v,G'.degree v=2*(Finset.univ.filter (H' v)).card) →
      (∀u,r∣(Finset.univ.filter (fun v=>H' v u)).card) →
      G'≤P → (∀v u,H' v u→Hbase v u) →
      IsResourceAbsorber (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=r))
        (ordinaryHostResources G' H') A):
    HasOrdinaryWheelDecomposition Q H r:=by
  let Host:=ordinaryHostResources Q H
  let K:=A∪D
  have hK:K⊆Host:=Finset.union_subset hA hD
  have hdecK:=resource_decomposition_union
    (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=r)) A D hdecA hdecD hdis
  obtain ⟨Gterm,Hterm,hEq,hb,hd,hsub,hs⟩:=
    ordinary_resource_terminal_remainder_balance Q P F H Hbase r hbal hdiv K hK hdecK
  have hr:ordinaryHostResources Gterm Hterm⊆ordinaryRootResources W B:=by rw [hEq];exact hroot
  have hz:(ordinaryPhysicalGraph Gterm Hterm).support.toFinset.card≤m:=
    (ordinary_terminal_root_geometry Gterm Hterm W B hr).1.trans hsize
  have hg: Gterm≤P ∧ (∀v u,Hterm v u→Hbase v u):=
    ordinary_terminal_root_local_host Gterm P Hterm Hbase W B hr
      (fun v hv w hw he=>hP v hv w hw (hsub he))
      (fun v hv u hu he=>hH v hv u hu (hs v u he))
  have habs:HasResourceDecomposition
      (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=r))
      (A∪ordinaryHostResources Gterm Hterm):=(hres Gterm Hterm hr hz hb hd hg.1 hg.2).2.2
  have hdisDT:Disjoint D (A∪ordinaryHostResources Gterm Hterm):=by
    apply Finset.disjoint_left.mpr
    intro e he hmem
    rcases Finset.mem_union.mp hmem with ha|ht
    · exact Finset.disjoint_left.mp hdis ha he
    · rw [hEq] at ht
      exact (Finset.mem_sdiff.mp ht).2 (Finset.mem_union_right A he)
  have hall:=resource_decomposition_union
    (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=r)) D
      (A∪ordinaryHostResources Gterm Hterm) hdecD habs hdisDT
  have hunion:D∪(A∪ordinaryHostResources Gterm Hterm)=Host:=by
    rw [hEq]
    ext e
    simp only [Finset.mem_union,Finset.mem_sdiff]
    have ha:=hA
    have hd:=hD
    constructor
    · rintro (he|he|⟨he,_⟩)
      · exact hd he
      · exact ha he
      · exact he
    · intro he
      by_cases heA:e∈A
      · exact Or.inr (Or.inl heA)
      by_cases heD:e∈D
      · exact Or.inl heD
      exact Or.inr (Or.inr ⟨he,by simpa [K] using And.intro heA heD⟩)
  rw [hunion] at hall
  exact ordinary_host_decomposition_forget Host hall
end Oberwolfach
