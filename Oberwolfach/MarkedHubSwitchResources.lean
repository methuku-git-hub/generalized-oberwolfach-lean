module

public import Oberwolfach.MarkedNewVertexEdgeAvoidance
public import Oberwolfach.MarkedClassFactorTrade

@[expose] public section

/-! Resource information supplied by the two actual hub-switch factors.
Every rim edge has a new auxiliary endpoint, whereas spokes on the retained
roots have exactly the two specified hubs. These are consequences of the
factor cover and root independence, not extra construction assumptions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {m:ℕ} {π:Equiv.Perm V} {b:ℕ}

 def MarkedSwitchResource (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (Y Z:Finset V) (u u':U):Finset V⊕(V×U)→Prop
  | .inl e=>∃ a:E⊕K,markedPhysicalEdge tail head ktail khead π a=e∧
      Sum.elim tail ktail a∈Y∪Z∧Sum.elim head khead a∈Y∪Z∧
      (Sum.elim tail ktail a∈Y∨Sum.elim head khead a∈Y)
  | .inr vu=>vu.1∈Y∪Z∧(vu.2=u∨vu.2=u')

 theorem marked_switch_resource_supported (Y Z:Finset V) (u u':U)
    (e:Finset V⊕(V×U)) (he:MarkedSwitchResource tail head ktail khead π Y Z u u' e):
    MarkedResourceSupported tail head ktail khead π (Y∪Z) e:=by
  cases e with
  | inl e=>obtain ⟨a,ha,h₁,h₂,_⟩:=he;exact ⟨a,ha,h₁,h₂⟩
  | inr vu=>exact he.1

 theorem marked_class_factor_switch_resources (hm:1≤m)
    (A B Y Z:Finset V) (hYZ:Disjoint Y Z) (u u':U)
    (M:Finset (ClassMarkedCycle tail head ktail khead m π b A B))
    (hcover:M.biUnion classMarkedCycleVertices⊆Y∪Z)
    (hcap:∀ C∈M,(classMarkedCycleVertices C∩Z).card≤1):
    ∀ e∈M.biUnion (fun C=>markedCycleResourcesAtHub (classMarkedCycleAsMarked C) u),
      MarkedSwitchResource tail head ktail khead π Y Z u u' e:=by
  intro e he
  obtain ⟨C,hC,he⟩:=Finset.mem_biUnion.mp he
  have hT:Finset.univ.image (classMarkedCycleAsMarked C).val⊆Y∪Z:=by
    intro v hv
    exact hcover (Finset.mem_biUnion.mpr ⟨C,hC,hv⟩)
  rcases Finset.mem_union.mp he with he|he
  · obtain ⟨f,hf,rfl⟩:=Finset.mem_image.mp he
    obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hf
    have hend:=markedCycleTypedEdge_endpoints tail head ktail khead m π b (classMarkedCycleAsMarked C) i
    refine ⟨markedCycleTypedEdge tail head ktail khead m π b (classMarkedCycleAsMarked C) i,hi,?_,?_,?_⟩
    · rw [hend.1];exact hT (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    · rw [hend.2];exact hT (Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩)
    · rw [hend.1,hend.2]
      exact marked_cycle_arc_has_new_endpoint hm (classMarkedCycleAsMarked C) Y Z hT (hcap C hC) i
  · obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp he
    exact ⟨hT hv,Or.inl rfl⟩

 theorem marked_switch_resource_swap (Y Z:Finset V) (u u':U) (e:Finset V⊕(V×U)):
    MarkedSwitchResource tail head ktail khead π Y Z u u' e↔
      MarkedSwitchResource tail head ktail khead π Y Z u' u e:=by
  cases e with
  | inl e=>rfl
  | inr vu=>exact and_congr_right (fun _=>or_comm)

 theorem marked_two_factor_switch_resources (hm:1≤m)
    (A B Y Z:Finset V) (hYZ:Disjoint Y Z) (u u':U)
    (M₀ M₁:Finset (ClassMarkedCycle tail head ktail khead m π b A B))
    (h₀:M₀.biUnion classMarkedCycleVertices=Y)
    (h₁:M₁.biUnion classMarkedCycleVertices=Y∪Z)
    (hcap:∀ C∈M₁,(classMarkedCycleVertices C∩Z).card≤1):
    let P:=M₁.biUnion (fun C=>markedCycleResourcesAtHub (classMarkedCycleAsMarked C) u)∪
      M₀.biUnion (fun C=>markedCycleResourcesAtHub (classMarkedCycleAsMarked C) u')
    let N:=M₁.biUnion (fun C=>markedCycleResourcesAtHub (classMarkedCycleAsMarked C) u')∪
      M₀.biUnion (fun C=>markedCycleResourcesAtHub (classMarkedCycleAsMarked C) u)
    ∀ e∈P∪N,MarkedSwitchResource tail head ktail khead π Y Z u u' e:=by
  dsimp only
  have hcap₀:∀ C∈M₀,(classMarkedCycleVertices C∩Z).card≤1:=by
    intro C hC
    have hd:Disjoint (classMarkedCycleVertices C) Z:=hYZ.mono_left (by
      intro v hv;rw [←h₀];exact Finset.mem_biUnion.mpr ⟨C,hC,hv⟩)
    rw [Finset.disjoint_iff_inter_eq_empty.mp hd]
    simp
  have hcov₀:M₀.biUnion classMarkedCycleVertices⊆Y∪Z:=by rw [h₀];exact Finset.subset_union_left
  have hcov₁:M₁.biUnion classMarkedCycleVertices⊆Y∪Z:=by rw [h₁]
  have h0:=marked_class_factor_switch_resources hm A B Y Z hYZ u u' M₀ hcov₀ hcap₀
  have h1:=marked_class_factor_switch_resources hm A B Y Z hYZ u u' M₁ hcov₁ hcap
  have h0':=marked_class_factor_switch_resources hm A B Y Z hYZ u' u M₀ hcov₀ hcap₀
  have h1':=marked_class_factor_switch_resources hm A B Y Z hYZ u' u M₁ hcov₁ hcap
  intro e he
  rcases Finset.mem_union.mp he with he|he
  · rcases Finset.mem_union.mp he with he|he
    · exact h1 e he
    · exact (marked_switch_resource_swap Y Z u' u e).mp (h0' e he)
  · rcases Finset.mem_union.mp he with he|he
    · exact (marked_switch_resource_swap Y Z u' u e).mp (h1' e he)
    · exact h0 e he

end Oberwolfach
