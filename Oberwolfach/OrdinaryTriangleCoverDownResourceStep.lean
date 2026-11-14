module

public import Oberwolfach.OrdinaryTriangleCoverDownResult
public import Oberwolfach.OrdinaryTriangleDecompositionHost

@[expose] public section
/-! A conditional triangle cover-down gives the exact conflict-respecting
resource step required by the balanced level-chain interface. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 2048
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_cover_down_resource_step
    (P Q F:SimpleGraph V) (Hbase H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (hQP:Q≤P) (hQF:Disjoint Q F) (hH:∀v u,H v u→Hbase v u)
    (hstep:OrdinaryTriangleCoverDownResult Q H X Z):
    ∃T:Finset (Sym2 V⊕(V×U)),T⊆ordinaryHostResources Q H ∧ T⊆ordinaryRootResources X Z ∧
      HasResourceDecomposition (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=3))
        (ordinaryHostResources Q H\T):=by
  obtain ⟨A,S,hAQ,hSH,hA,hinner,hspoke,_,_⟩:=hstep
  let Next:=ordinaryHostResources (Q\A) (fun v u=>H v u∧¬S v u)
  let Used:=ordinaryHostResources A S
  have hUsed:Used⊆ordinaryHostResources Q H:=by
    intro e he
    cases e with
    | inl e=>
      rw [ordinaryHostResources_rim] at he ⊢
      exact SimpleGraph.edgeSet_mono hAQ he
    | inr vu=>
      rcases vu with ⟨v,u⟩
      rw [ordinaryHostResources_spoke] at he ⊢
      exact hSH v u he
  have hNext:Next=ordinaryHostResources Q H\Used:=ordinaryHostResources_sdiff Q A H S
  have hsub:Next⊆ordinaryHostResources Q H:=by rw [hNext];exact Finset.sdiff_subset
  have hroot:Next⊆ordinaryRootResources X Z:=by
    intro e he
    cases e with
    | inl e=>
      induction e using Sym2.ind with
      | _ v w=>
        have he':(Q\A).Adj v w:=(ordinaryHostResources_rim (Q\A) _ s(v,w)).mp he
        have hvw:=(spanningRestriction_adj Q X v w).mp (hinner he')
        exact ordinaryRootResources_rim X Z v w hvw.2.1 hvw.2.2
    | inr vu=>
      rcases vu with ⟨v,u⟩
      have he':H v u∧¬S v u:=(ordinaryHostResources_spoke (Q\A) _ v u).mp he
      exact ordinaryRootResources_spoke X Z v u (hspoke v u he').1 (hspoke v u he').2
  have hdec:=ordinary_triangle_decomposition_in_ambient_host P A F Hbase S
    (hAQ.trans hQP) (hQF.mono_left hAQ) (fun v u h=>hH v u (hSH v u h)) hA
  refine ⟨Next,hsub,hroot,?_⟩
  have heq:ordinaryHostResources Q H\Next=Used:=by
    rw [hNext]
    ext e
    have hh:=fun he=>hUsed (x:=e) he
    simp only [Finset.mem_sdiff]
    tauto
  rw [heq]
  exact hdec
end Oberwolfach
