module

public import Oberwolfach.OrdinaryTriangleControlledResourceStep

@[expose] public section
/-! A controlled triangle level supplies the generic level-chain step once
the chosen analytic invariant is shown to survive its actual inner deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_controlled_good_level_step
    (P Q F:SimpleGraph V) (Hbase H:V→U→Prop) (X:Finset V) (Z:Finset U) (t:ℝ)
    (Good:Finset (Sym2 V⊕(V×U))→Prop)
    (hQP:Q≤P) (hQF:Disjoint Q F) (hH:∀v u,H v u→Hbase v u)
    (hstep:OrdinaryTriangleControlledCoverDownResult Q H X Z t)
    (hpreserve:∀A:SimpleGraph V,∀S:V→U→Prop,A≤Q→(∀v u,S v u→H v u)→
      HasResourceDecomposition (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=3)) (ordinaryHostResources A S)→
      ordinaryHostResources (Q\A) (fun v u=>H v u∧¬S v u)⊆ordinaryRootResources X Z→
      (∀v,(Q\A).degree v=2*(Finset.univ.filter (fun u=>H v u∧¬S v u)).card)→
      (∀u,3∣(Finset.univ.filter (fun v=>H v u∧¬S v u)).card)→
      (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph A S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤t)→
      Good (ordinaryHostResources (Q\A) (fun v u=>H v u∧¬S v u))):
    ∃T:Finset (Sym2 V⊕(V×U)),Good T ∧ T⊆ordinaryHostResources Q H ∧ T⊆ordinaryRootResources X Z ∧
      HasResourceDecomposition (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=3))
        (ordinaryHostResources Q H\T):=by
  obtain ⟨A,S,hAQ,hSH,hdec,hroot,hbal,hdiv,hbound⟩:=
    ordinary_triangle_controlled_resource_step P Q F Hbase H X Z t hQP hQF hH hstep
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
  have heq:ordinaryHostResources Q H\Next=Used:=by
    rw [hNext]
    ext e
    have hh:=fun he=>hUsed (x:=e) he
    simp only [Finset.mem_sdiff]
    tauto
  refine ⟨Next,hpreserve A S hAQ hSH hdec hroot hbal hdiv hbound,hsub,hroot,?_⟩
  rw [heq]
  exact hdec
end Oberwolfach
