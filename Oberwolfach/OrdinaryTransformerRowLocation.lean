module

public import Oberwolfach.OrdinaryTransformerVertexAvoidance

@[expose] public section

/-! Exact location of the positive wheel family: every row is an old
root or belongs to the supplied available row set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_transformer_positive_row_location
    (G Q F:SimpleGraph V) (H₀ H:V→U→Prop) (φ:V→V) (ψ:U→U) (r:ℕ)
    (A R:Finset V) (B:Finset U)
    (b:∀ v,G.neighborSet v≃({u:U // H₀ v u}×Fin 2))
    (σ:∀ v,Equiv.Perm (G.neighborSet v))
    (p:(G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c))
    (hbalance:∀ v,G.degree v=2*(Finset.univ.filter (H₀ v)).card)
    (hroot:∀ v∈G.support,v∈R∧φ v∈R)
    (hpA:∀ i,∀ v∈(p i).2.2.support,v∈A)
    (E:OrdinaryActualRimWheels G Q F H₀ H φ r B b σ p)
    (S:OrdinaryActualSpokeWheels G Q F H₀ H φ ψ r p)
    (D:∀ d:Σ v,G.neighborSet v,
      OrdinaryVertexWheelPair Q F H r d.1 (φ d.1)
        (transformerRimEndpoint G Q H₀ p d) (transformerSpokeEndpoint G Q H₀ b p d)
        (transformerAssignedHub G σ E.hub d))
    (hD:∀ d,∀ v∈rootWheelInternal (D d).first d.1 (transformerRimEndpoint G Q H₀ p d)
      (transformerSpokeEndpoint G Q H₀ b p d),v∈A) :
    let Plus:=Sum.elim E.first (Sum.elim S.first (fun d=>(D d).second))
    ∀ i,∀ v∈(ordinaryWheelRim (Plus i)).support,v∈R∪A := by
  dsimp only
  intro i v hv
  rcases i with i|(i|i)
  · rcases (E.first_support i v).mp hv with he|he|he
    · exact Finset.mem_union_left _ (he.symm ▸ (hroot _ (edge_out_adj G i).mem_support_left).1)
    · exact Finset.mem_union_left _ (he.symm ▸ (hroot _ (edge_out_adj G i).mem_support_right).1)
    · exact Finset.mem_union_right _ (hpA _ _ he)
  · rcases (S.first_support i v).mp hv with he|he
    · exact Finset.mem_union_left _ (he.symm ▸ (hroot _ (balanced_spoke_root_mem_support G H₀ hbalance i)).1)
    · exact Finset.mem_union_right _ (hpA _ _ he)
  · rcases ((D i).second_support v).mp hv with he|⟨hv,hne⟩
    · exact Finset.mem_union_left _ (he.symm ▸ (hroot _ i.2.property.mem_support_left).2)
    · apply Finset.mem_union_right
      by_cases hva:v=transformerRimEndpoint G Q H₀ p i
      · exact hva ▸ hpA _ _ (graphPathEndpoint_mem _ _)
      by_cases hvb:v=transformerSpokeEndpoint G Q H₀ b p i
      · exact hvb ▸ hpA _ _ (graphPathEndpoint_mem _ _)
      apply hD i v
      simp only [rootWheelInternal,Finset.mem_sdiff,Set.mem_toFinset,Finset.mem_insert,
        Finset.mem_singleton,hne,hva,hvb,false_or,not_false_eq_true,and_true]
      exact hv

end Oberwolfach
