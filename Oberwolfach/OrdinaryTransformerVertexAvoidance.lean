module

public import Oberwolfach.OrdinaryTransformerRootRestriction

@[expose] public section

/-! Every row vertex used by the positive wheel family either is an old
root or avoids any previously forbidden set avoided by the paths. This
tracks actual supports, including the two reused endpoint labels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

 theorem ordinary_transformer_positive_row_avoidance
    (G Q F:SimpleGraph V) (H₀ H:V→U→Prop) (φ:V→V) (ψ:U→U) (r:ℕ)
    (R W W₀:Finset V) (B:Finset U) (hWW:W₀⊆W)
    (b:∀ v,G.neighborSet v≃({u:U // H₀ v u}×Fin 2))
    (σ:∀ v,Equiv.Perm (G.neighborSet v))
    (p:(G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c))
    (hbalance:∀ v,G.degree v=2*((Finset.univ:Finset U).filter (H₀ v)).card)
    (hroot:∀ v∈G.support,v∈R∧φ v∈R)
    (hpW:∀ i,∀ v∈(p i).2.2.support,v∉W₀)
    (E:OrdinaryActualRimWheels G Q F H₀ H φ r B b σ p)
    (S:OrdinaryActualSpokeWheels G Q F H₀ H φ ψ r p)
    (D:∀ d:Σ v,G.neighborSet v,
      OrdinaryVertexWheelPair Q F H r d.1 (φ d.1)
        (transformerRimEndpoint G Q H₀ p d) (transformerSpokeEndpoint G Q H₀ b p d)
        (transformerAssignedHub G σ E.hub d))
    (hD:∀ d,∀ v∈rootWheelInternal (D d).first d.1 (transformerRimEndpoint G Q H₀ p d)
      (transformerSpokeEndpoint G Q H₀ b p d),v∉W):
    let Plus:=Sum.elim E.first (Sum.elim S.first (fun d=>(D d).second))
    ∀ i,∀ v∈(ordinaryWheelRim (Plus i)).support,v∈W₀→v∈R:=by
  dsimp only
  intro i v hv hW₀
  rcases i with i|(i|i)
  · rcases (E.first_support i v).mp hv with he|he|he
    · exact he.symm ▸ (hroot _ (edge_out_adj G i).mem_support_left).1
    · exact he.symm ▸ (hroot _ (edge_out_adj G i).mem_support_right).1
    · exact (hpW _ _ he hW₀).elim
  · rcases (S.first_support i v).mp hv with he|he
    · exact he.symm ▸ (hroot _ (balanced_spoke_root_mem_support G H₀ hbalance i)).1
    · exact (hpW _ _ he hW₀).elim
  · rcases ((D i).second_support v).mp hv with he|⟨hv,hne⟩
    · exact he.symm ▸ (hroot _ i.2.property.mem_support_left).2
    · have ha:transformerRimEndpoint G Q H₀ p i∉W₀:=hpW _ _ (graphPathEndpoint_mem _ _)
      have hb:transformerSpokeEndpoint G Q H₀ b p i∉W₀:=hpW _ _ (graphPathEndpoint_mem _ _)
      have hva:v≠transformerRimEndpoint G Q H₀ p i:=fun he=>ha (he ▸ hW₀)
      have hvb:v≠transformerSpokeEndpoint G Q H₀ b p i:=fun he=>hb (he ▸ hW₀)
      have hint:v∈rootWheelInternal (D i).first i.1 (transformerRimEndpoint G Q H₀ p i)
          (transformerSpokeEndpoint G Q H₀ b p i):=by
        simp only [rootWheelInternal,Finset.mem_sdiff,Set.mem_toFinset,Finset.mem_insert,
          Finset.mem_singleton,hne,hva,hvb,false_or,not_false_eq_true,and_true]
        exact hv
      exact (hD i v hint (hWW hW₀)).elim

end Oberwolfach
