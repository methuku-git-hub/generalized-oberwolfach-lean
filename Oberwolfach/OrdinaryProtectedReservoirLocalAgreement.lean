module

public import Oberwolfach.OrdinaryResourceRemovalLocalEdit
public import Oberwolfach.OrdinaryRootResources

@[expose] public section
/-! A terminal reservoir disjoint from an inner pair has zero edit cost on
that pair, regardless of its size elsewhere. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_protected_reservoir_induced_pair
    (Q:SimpleGraph V) (H:V→U→Prop) (K:Finset (Sym2 V⊕(V×U))) (X:Finset V) (Z:Finset U)
    (havoid:Disjoint K (ordinaryRootResources X Z)):
    (Q\ordinaryResourceRim Q K).induce (X:Set V)=Q.induce (X:Set V) ∧
    (fun (v:↥X) (u:↥Z)=>H v.val u.val∧¬(Sum.inr (v.val,u.val)∈K))=
      (fun (v:↥X) (u:↥Z)=>H v.val u.val):=by
  have ha:=ordinaryRootResources_avoid K X Z havoid
  constructor
  · ext v w
    simp only [SimpleGraph.induce_adj,SimpleGraph.sdiff_adj,ordinaryResourceRim]
    have hn:=ha.1 v.val v.property w.val w.property
    tauto
  · funext v u
    apply propext
    have hn:=ha.2 v.val v.property u.val u.property
    tauto

theorem ordinary_protected_reservoir_induced_physical
    (Q:SimpleGraph V) (H:V→U→Prop) (K:Finset (Sym2 V⊕(V×U))) (X:Finset V) (Z:Finset U)
    (havoid:Disjoint K (ordinaryRootResources X Z)):
    ordinaryPhysicalGraph ((Q\ordinaryResourceRim Q K).induce (X:Set V))
      (fun (v:↥X) (u:↥Z)=>H v.val u.val∧¬(Sum.inr (v.val,u.val)∈K))=
    ordinaryPhysicalGraph (Q.induce (X:Set V)) (fun (v:↥X) (u:↥Z)=>H v.val u.val):=by
  obtain ⟨hr,hs⟩:=ordinary_protected_reservoir_induced_pair Q H K X Z havoid
  rw [hr,hs]

theorem ordinary_protected_reservoir_nested_pair
    (Q:SimpleGraph V) (H:V→U→Prop) (K:Finset (Sym2 V⊕(V×U)))
    (X Y:Finset V) (Z B:Finset U) (hXY:X⊆Y) (hZB:Z⊆B)
    (havoid:Disjoint K (ordinaryRootResources Y B)):
    (Q\ordinaryResourceRim Q K).induce (X:Set V)=Q.induce (X:Set V) ∧
    (fun (v:↥X) (u:↥Z)=>H v.val u.val∧¬(Sum.inr (v.val,u.val)∈K))=
      (fun (v:↥X) (u:↥Z)=>H v.val u.val):=by
  have hsub:ordinaryRootResources X Z⊆ordinaryRootResources Y B:=
    ordinaryRootResources_contains _ _ _ ((ordinaryRootResources_rows X Z).trans hXY)
      ((ordinaryRootResources_hubs X Z).trans hZB)
  exact ordinary_protected_reservoir_induced_pair Q H K X Z (havoid.mono_right hsub)

theorem ordinary_protected_reservoir_local_reference
    (R Q:SimpleGraph V) (J H:V→U→Prop) (K:Finset (Sym2 V⊕(V×U)))
    (X Y:Finset V) (Z B:Finset U) (hXY:X⊆Y) (hZB:Z⊆B)
    (havoid:Disjoint K (ordinaryRootResources Y B)) (L:ℝ):
    let V₁:=↥X;let U₁:=↥Z;
    let R₁:=R.induce (X:Set V);let Q₁:=Q.induce (X:Set V);
    let J₁:=fun (v:V₁) (u:U₁)=>J v.val u.val;
    let H₁:=fun (v:V₁) (u:U₁)=>H v.val u.val;
    (∀a:V₁⊕U₁,((changed ((ordinaryPhysicalGraph R₁ J₁).neighborFinset a)
      ((ordinaryPhysicalGraph Q₁ H₁).neighborFinset a)).card:ℝ)≤L)→
    let G₁:=(Q\ordinaryResourceRim Q K).induce (X:Set V);
    let Hs₁:=fun (v:V₁) (u:U₁)=>H v.val u.val∧¬(Sum.inr (v.val,u.val)∈K);
    ∀a:V₁⊕U₁,((changed ((ordinaryPhysicalGraph R₁ J₁).neighborFinset a)
      ((ordinaryPhysicalGraph G₁ Hs₁).neighborFinset a)).card:ℝ)≤L:=by
  intro V₁ U₁ R₁ Q₁ J₁ H₁ hbase G₁ Hs₁ a
  obtain ⟨hr,hs⟩:=ordinary_protected_reservoir_nested_pair Q H K X Y Z B hXY hZB havoid
  have hp:ordinaryPhysicalGraph G₁ Hs₁=ordinaryPhysicalGraph Q₁ H₁:=by
    dsimp only [G₁,Hs₁,Q₁,H₁]
    rw [hr,hs]
  have hn:(ordinaryPhysicalGraph G₁ Hs₁).neighborFinset a=(ordinaryPhysicalGraph Q₁ H₁).neighborFinset a:=by
    ext b
    simp only [SimpleGraph.mem_neighborFinset]
    rw [hp]
  rw [hn]
  convert hbase a using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
