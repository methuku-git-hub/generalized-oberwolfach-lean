module

public import Oberwolfach.OrdinaryTransformerOldSpokes

@[expose] public section

/-! On the old row and hub sets, the positive wheel family contains
only the original root edges. New vertex wheels have just one old row
vertex; fresh hubs cannot create old root spokes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

 theorem ordinary_transformer_positive_root_restriction
    (G Q F:SimpleGraph V) (H₀ H:V→U→Prop) (φ:V→V) (ψ:U→U) (r:ℕ)
    (R W:Finset V) (B:Finset U) (hRW:R⊆W)
    (b:∀ v,G.neighborSet v≃({u:U // H₀ v u}×Fin 2))
    (σ:∀ v,Equiv.Perm (G.neighborSet v))
    (p:(G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c))
    (hpR:∀ i,∀ v∈(p i).2.2.support,v∉R)
    (E:OrdinaryActualRimWheels G Q F H₀ H φ r B b σ p)
    (S:OrdinaryActualSpokeWheels G Q F H₀ H φ ψ r p)
    (D:∀ d:Σ v,G.neighborSet v,
      OrdinaryVertexWheelPair Q F H r d.1 (φ d.1)
        (transformerRimEndpoint G Q H₀ p d) (transformerSpokeEndpoint G Q H₀ b p d)
        (transformerAssignedHub G σ E.hub d))
    (hD:∀ d,∀ v∈rootWheelInternal (D d).first d.1 (transformerRimEndpoint G Q H₀ p d)
      (transformerSpokeEndpoint G Q H₀ b p d),v∉W):
    let Plus:=Sum.elim E.first (Sum.elim S.first (fun d=>(D d).second))
    (∀ v∈R,∀ v'∈R,(wheelFamilyRim Plus).Adj v v'→G.Adj v v')∧
    (∀ v∈R,∀ u∈B,wheelFamilySpokes Plus v u→H₀ v u):=by
  dsimp only
  have hS (i:{e:V×U // H₀ e.1 e.2}) (v:V) (hv:v∈R)
      (hi:v∈(ordinaryWheelRim (S.first i)).support):v=i.val.1:=
    ((S.first_support i v).mp hi).resolve_right (fun h=>hpR _ _ h hv)
  have hE (i:G.edgeFinset) (v:V) (hv:v∈R)
      (hi:v∈(ordinaryWheelRim (E.first i)).support):v=i.val.out.1∨v=i.val.out.2:=by
    rcases (E.first_support i v).mp hi with h|h|h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hpR _ _ h hv).elim
  have hDroot (i:Σ v,G.neighborSet v) (v:V) (hv:v∈R)
      (hi:v∈(ordinaryWheelRim (D i).second).support):v=φ i.1:=by
    rcases ((D i).second_support v).mp hi with he|⟨hi,hne⟩
    · exact he
    · have ha:transformerRimEndpoint G Q H₀ p i∉R:=hpR _ _ (graphPathEndpoint_mem _ _)
      have hb:transformerSpokeEndpoint G Q H₀ b p i∉R:=hpR _ _ (graphPathEndpoint_mem _ _)
      have hva:v≠transformerRimEndpoint G Q H₀ p i:=fun he=>ha (he ▸ hv)
      have hvb:v≠transformerSpokeEndpoint G Q H₀ b p i:=fun he=>hb (he ▸ hv)
      have hint:v∈rootWheelInternal (D i).first i.1 (transformerRimEndpoint G Q H₀ p i)
          (transformerSpokeEndpoint G Q H₀ b p i):=by
        simp only [rootWheelInternal,Finset.mem_sdiff,Set.mem_toFinset,Finset.mem_insert,
          Finset.mem_singleton,hne,hva,hvb,false_or,not_false_eq_true,and_true]
        exact hi
      exact (hD i v hint (hRW hv)).elim
  constructor
  · intro v hv v' hv' he
    obtain ⟨i,hi⟩:=SimpleGraph.iSup_adj.mp he
    rcases i with i|(i|i)
    · have h1:=hE i v hv hi.mem_support_left
      have h2:=hE i v' hv' hi.mem_support_right
      rcases h1 with h1|h1 <;> rcases h2 with h2|h2
      · exact (hi.ne (h1.trans h2.symm)).elim
      · exact h1.symm ▸ h2.symm ▸ edge_out_adj G i
      · exact h1.symm ▸ h2.symm ▸ (edge_out_adj G i).symm
      · exact (hi.ne (h1.trans h2.symm)).elim
    · exact (hi.ne ((hS i v hv hi.mem_support_left).trans (hS i v' hv' hi.mem_support_right).symm)).elim
    · exact (hi.ne ((hDroot i v hv hi.mem_support_left).trans (hDroot i v' hv' hi.mem_support_right).symm)).elim
  · rintro v hv u hu ⟨i,hi,hvi⟩
    rcases i with i|(i|i)
    · change ordinaryWheelHub (E.first i)=u at hi
      rw [E.first_hub] at hi
      exact (E.hub_avoid i (hi.symm ▸ hu)).elim
    · have hvr:=hS i v hv hvi
      change ordinaryWheelHub (S.first i)=u at hi
      rw [S.first_hub] at hi
      exact hvr.symm ▸ hi ▸ i.property
    · change ordinaryWheelHub (D i).second=u at hi
      rw [(D i).second_hub] at hi
      exact (E.hub_avoid _ (hi.symm ▸ hu)).elim

end Oberwolfach
