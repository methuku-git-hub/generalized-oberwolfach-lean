module

public import Oberwolfach.MarkedHostDiagram
public import Oberwolfach.OrdinaryDiagramEndpoints

@[expose] public section

/-! Endpoint and active-hub identities for the alternating marked chain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K A S:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b m M:ℕ}
    {original:Finset (Finset V⊕(V×U))} {W Z O:Finset V} {B O':Finset U}

theorem MarkedHostDiagram.chain_endpoints
    (D:MarkedHostDiagram m M tail head ktail khead H₀ HK π b original W Z B O O' A S):
    ∀ j:Fin 4,((D.P j).source=finiteFiveAt D.D j.val∧(D.P j).image=finiteFiveAt D.D (j.val+1))∨
      ((D.P j).source=finiteFiveAt D.D (j.val+1)∧(D.P j).image=finiteFiveAt D.D j.val):=by
  intro j
  rw [D.source,D.image]
  fin_cases j <;> simp [finiteFiveAt]

theorem MarkedHostDiagram.chain_disjoint
    (D:MarkedHostDiagram m M tail head ktail khead H₀ HK π b original W Z B O O' A S):
    ∀ i,i≤4→∀ j,j≤4→i≠j→Disjoint (finiteFiveAt D.D i) (finiteFiveAt D.D j):=by
  intro i hi j hj hij
  rw [show finiteFiveAt D.D i=D.D ⟨i,by omega⟩ from finiteFiveAt_apply D.D ⟨i,by omega⟩,
    show finiteFiveAt D.D j=D.D ⟨j,by omega⟩ from finiteFiveAt_apply D.D ⟨j,by omega⟩]
  exact D.disjoint _ _ (fun h=>hij (congrArg Fin.val h))

theorem MarkedHostDiagram.root_resources_supported
    (D:MarkedHostDiagram m M tail head ktail khead H₀ HK π b original W Z B O O' A S):
    ∀ j,∀ e∈(D.P j).source∪(D.P j).image,MarkedOldResource tail head ktail khead π D.rows D.hubs e:=by
  intro j e he
  rw [D.source,D.image] at he
  fin_cases j <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three] at he
  all_goals rcases Finset.mem_union.mp he with he|he
  all_goals exact D.supported _ e he

theorem MarkedHostDiagram.active_hubs
    (D:MarkedHostDiagram m M tail head ktail khead H₀ HK π b original W Z B O O' A S)
    (j:Fin 4) (s:S):(D.P j).u s∈D.hubs∧(D.P j).u' s∈D.hubs:=by
  have hs:Sum.inr ((D.P j).row s,(D.P j).u s)∈(D.P j).source:=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s,Finset.mem_univ _,rfl⟩)
  have ht:Sum.inr ((D.P j).φ ((D.P j).row s),(D.P j).u' s)∈(D.P j).image:=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s,Finset.mem_univ _,rfl⟩)
  exact ⟨(D.root_resources_supported j _ (Finset.mem_union_left _ hs)).2,
    (D.root_resources_supported j _ (Finset.mem_union_right _ ht)).2⟩

def markedDiagramAbsorberEdges
    (D:MarkedHostDiagram m M tail head ktail khead H₀ HK π b original W Z B O O' A S)
    (C:Fin 4→Finset (Finset V⊕(V×U))):Finset (Finset V⊕(V×U)):=
  D.extra∪transformerChainEdges (finiteFiveAt D.D) (finiteTransformerAt C) 4∪D.D 4

theorem markedDiagramAbsorberEdges_membership
    (D:MarkedHostDiagram m M tail head ktail khead H₀ HK π b original W Z B O O' A S)
    (C:Fin 4→Finset (Finset V⊕(V×U))) (e:Finset V⊕(V×U))
    (he:e∈markedDiagramAbsorberEdges D C):
    e∈D.extra∨(∃ i:Fin 4,e∈C i)∨∃ i:Fin 5,i≠0∧e∈D.D i:=by
  rcases Finset.mem_union.mp he with he|he
  · rcases Finset.mem_union.mp he with he|he
    · exact Or.inl he
    · rcases (mem_transformerChainEdges _ _ _ _).mp he with ⟨i,hi,he⟩|⟨i,hi0,hi,he⟩
      · exact Or.inr (Or.inl ⟨⟨i,hi⟩,by simpa only [finiteTransformerAt_apply C ⟨i,hi⟩] using he⟩)
      · exact Or.inr (Or.inr ⟨⟨i,by omega⟩,by intro h;have hh:=congrArg Fin.val h;dsimp at hh;omega,
          by simpa only [finiteFiveAt_apply D.D ⟨i,by omega⟩] using he⟩)
  · exact Or.inr (Or.inr ⟨4,by decide,he⟩)

end Oberwolfach
