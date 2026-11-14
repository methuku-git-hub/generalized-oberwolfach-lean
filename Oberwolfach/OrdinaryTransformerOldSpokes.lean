module

public import Oberwolfach.OrdinaryTransformerVertexStageRealization

@[expose] public section

/-! Identify every old-hub spoke on the actual spoke paths. Fresh hubs
cannot contribute such spokes. Distinct spoke paths are disjoint, even
when the image map on hubs is not injective. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

 theorem ordinary_transformer_old_spokes
    (G Q F:SimpleGraph V) (H₀ H:V→U→Prop) (φ:V→V) (ψ:U→U) (r:ℕ)
    (R:Finset V) (B:Finset U)
    (b:∀ v,G.neighborSet v≃({u:U // H₀ v u}×Fin 2))
    (σ:∀ v,Equiv.Perm (G.neighborSet v))
    (p:(G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c))
    (hbalance:∀ v,G.degree v=2*((Finset.univ:Finset U).filter (H₀ v)).card)
    (hroot:∀ v∈G.support,v∈R∧φ v∈R)
    (hpR:∀ i,∀ v∈(p i).2.2.support,v∉R)
    (hdis:∀ i j,i≠j→Disjoint (p i).2.2.support.toFinset (p j).2.2.support.toFinset)
    (E:OrdinaryActualRimWheels G Q F H₀ H φ r B b σ p)
    (S:OrdinaryActualSpokeWheels G Q F H₀ H φ ψ r p)
    (D:∀ d:Σ v,G.neighborSet v,
      OrdinaryVertexWheelPair Q F H r d.1 (φ d.1)
        (transformerRimEndpoint G Q H₀ p d) (transformerSpokeEndpoint G Q H₀ b p d)
        (transformerAssignedHub G σ E.hub d)):
    let Plus:=Sum.elim E.first (Sum.elim S.first (fun d=>(D d).second))
    let Minus:=Sum.elim E.second (Sum.elim S.second (fun d=>(D d).first))
    ∀ j:{e:V×U // H₀ e.1 e.2},∀ v∈(p (.inr j)).2.2.support,∀ z∈B,
      (wheelFamilySpokes Plus v z↔z=j.val.2)∧
      (wheelFamilySpokes Minus v z↔z=ψ j.val.2):=by
  dsimp only
  intro j v hv z hz
  have hjR:v∉R:=hpR _ _ hv
  have hsame (i:{e:V×U // H₀ e.1 e.2}) (hi:v∈(p (.inr i)).2.2.support):i=j:=by
    by_contra hij
    exact Finset.disjoint_left.mp (hdis (.inr i) (.inr j) (fun he=>hij (Sum.inr.inj he)))
      (List.mem_toFinset.mpr hi) (List.mem_toFinset.mpr hv)
  have hfirst (i:{e:V×U // H₀ e.1 e.2}) (hi:v∈(ordinaryWheelRim (S.first i)).support):i=j:=by
    rcases (S.first_support i v).mp hi with he|hi
    · exact (hjR (he.symm ▸ (hroot _ (balanced_spoke_root_mem_support G H₀ hbalance i)).1)).elim
    · exact hsame i hi
  have hsecond (i:{e:V×U // H₀ e.1 e.2}) (hi:v∈(ordinaryWheelRim (S.second i)).support):i=j:=by
    rcases (S.second_support i v).mp hi with he|hi
    · exact (hjR (he.symm ▸ (hroot _ (balanced_spoke_root_mem_support G H₀ hbalance i)).2)).elim
    · exact hsame i hi
  constructor
  · constructor
    · rintro ⟨i,hi,hv'⟩
      rcases i with i|(i|i)
      · change ordinaryWheelHub (E.first i)=z at hi
        rw [E.first_hub] at hi
        exact (E.hub_avoid i (hi.symm ▸ hz)).elim
      · change v∈(ordinaryWheelRim (S.first i)).support at hv'
        have hij:=hfirst i hv'
        subst i
        change ordinaryWheelHub (S.first j)=z at hi
        exact ((S.first_hub j).symm.trans hi).symm
      · change ordinaryWheelHub (D i).second=z at hi
        rw [(D i).second_hub] at hi
        exact (E.hub_avoid _ (hi.symm ▸ hz)).elim
    · intro he
      refine ⟨.inr (.inl j),?_,?_⟩
      · exact (S.first_hub j).trans he.symm
      · exact (S.first_support j v).mpr (Or.inr hv)
  · constructor
    · rintro ⟨i,hi,hv'⟩
      rcases i with i|(i|i)
      · change ordinaryWheelHub (E.second i)=z at hi
        rw [E.second_hub] at hi
        exact (E.hub_avoid i (hi.symm ▸ hz)).elim
      · change v∈(ordinaryWheelRim (S.second i)).support at hv'
        have hij:=hsecond i hv'
        subst i
        change ordinaryWheelHub (S.second j)=z at hi
        exact ((S.second_hub j).symm.trans hi).symm
      · change ordinaryWheelHub (D i).first=z at hi
        rw [(D i).first_hub] at hi
        exact (E.hub_avoid _ (hi.symm ▸ hz)).elim
    · intro he
      refine ⟨.inr (.inl j),?_,?_⟩
      · exact (S.second_hub j).trans he.symm
      · exact (S.second_support j v).mpr (Or.inr hv)

end Oberwolfach
