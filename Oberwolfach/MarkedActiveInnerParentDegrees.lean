module

public import Oberwolfach.MarkedActiveDomainSizeBounds

@[expose] public section

/-! Parent graph degrees into the actual inner difference sets. Roots range
over the ambient active type; no assertion is inferred from an induced
subgraph alone. The change of the hub-dependent target is charged explicitly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V VA U UA:Type} [Fintype V] [Fintype VA] [Fintype U] [Fintype UA]
  [DecidableEq V] [DecidableEq VA] [DecidableEq U] [DecidableEq UA]

theorem graph_neighbourhood_embedding_card (f:VA↪V) (P:SimpleGraph V) (X:Finset VA) (x:VA):
    ((P.comap f).neighborFinset x∩X).card=(P.neighborFinset (f x)∩X.image f).card:=by
  have he:((P.comap f).neighborFinset x∩X).image f=P.neighborFinset (f x)∩X.image f:=by
    ext y
    simp only [Finset.mem_image,Finset.mem_inter,SimpleGraph.mem_neighborFinset,SimpleGraph.comap_adj]
    constructor
    · rintro ⟨z,⟨hz,hX⟩,rfl⟩;exact ⟨hz,⟨z,hX,rfl⟩⟩
    · rintro ⟨hy,z,hX,rfl⟩;exact ⟨z,⟨hy,hX⟩,rfl⟩
  rw [←he,Finset.card_image_of_injective _ f.injective]

theorem marked_active_inner_parent_degrees
    (f:VA↪V) (g:UA↪U) (P:SimpleGraph V)
    (I T:Finset V) (J W:Finset U) (X:Finset VA) (Z:Finset UA)
    (hX:X.image f=I\T) (hZ:Z.image g=J\W) (hW:W⊆J)
    (rho gamma err:ℝ) (hrho:0<rho) (hg:0≤gamma)
    (hT:(T.card:ℝ)≤(gamma/2)*I.card)
    (hparent:∀ v,|((P.neighborFinset v∩I).card:ℝ)-2*J.card/rho|≤err)
    (hmin:∀ v,(1/2+gamma)*I.card≤((P.neighborFinset v∩I).card:ℝ)):
    (∀ x,|(((P.comap f).neighborFinset x∩X).card:ℝ)-2*Z.card/rho|
      ≤err+T.card+2*W.card/rho)∧
    (∀ x,(1/2+gamma/2)*X.card≤((X∩(P.comap f).neighborFinset x).card:ℝ)):=by
  have hZcard:Z.card=(J\W).card:=by
    rw [←hZ,Finset.card_image_of_injective _ g.injective]
  have hJcard:(J.card:ℝ)=Z.card+W.card:=by
    exact_mod_cast (show J.card=Z.card+W.card by rw [hZcard];exact (Finset.card_sdiff_add_card_eq_card hW).symm)
  have hXle:(X.card:ℝ)≤I.card:=by
    have hh: X.card=(I\T).card:=by rw [←hX,Finset.card_image_of_injective _ f.injective]
    rw [hh];exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : I\T⊆I)
  have hcounts (x:VA):
      (((P.comap f).neighborFinset x∩X).card:ℝ)≤(P.neighborFinset (f x)∩I).card∧
      ((P.neighborFinset (f x)∩I).card:ℝ)≤((P.comap f).neighborFinset x∩X).card+T.card:=by
    have he:P.neighborFinset (f x)∩(I\T)=(P.neighborFinset (f x)∩I)\T:=by ext y;simp;tauto
    rw [graph_neighbourhood_embedding_card f P X x,hX,he]
    constructor
    · exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : (P.neighborFinset (f x)∩I)\T⊆P.neighborFinset (f x)∩I)
    · have hc:=Finset.card_sdiff_add_card_inter (P.neighborFinset (f x)∩I) T
      have hle:((P.neighborFinset (f x)∩I)∩T).card≤T.card:=Finset.card_le_card Finset.inter_subset_right
      exact_mod_cast (show (P.neighborFinset (f x)∩I).card≤((P.neighborFinset (f x)∩I)\T).card+T.card by omega)
  have htarget:2*(J.card:ℝ)/rho=2*Z.card/rho+2*W.card/rho:=by rw [hJcard];ring
  have hW0:0≤2*(W.card:ℝ)/rho:=by positivity
  constructor
  · intro x
    have hc:=hcounts x
    have hp:=abs_le.mp (hparent (f x))
    rw [htarget] at hp
    have ht0:0≤(T.card:ℝ):=Nat.cast_nonneg _
    apply abs_le.mpr
    constructor <;> linarith only [hc.1,hc.2,hp.1,hp.2,ht0,hW0]
  · intro x
    have hc:=(hcounts x).2
    have hp:=hmin (f x)
    have hh:=mul_le_mul_of_nonneg_left hXle (show 0≤1/2+gamma/2 by positivity)
    rw [Finset.inter_comm]
    nlinarith only [hc,hp,hT,hh]

end Oberwolfach
