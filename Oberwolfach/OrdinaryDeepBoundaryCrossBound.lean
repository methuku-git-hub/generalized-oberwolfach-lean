module

public import Oberwolfach.OrdinaryProtectedInnerPersistence
public import Oberwolfach.OrdinaryCrossBalanceDeletionTransferAt

@[expose] public section
/-! An earlier deletion protecting a deeper pair has small cross discrepancy
whenever its recorded deep-boundary degree is small. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_deep_boundary_cross_bound
    (R:SimpleGraph V) (S:V→U→Prop) (X T I:Finset V) (Z W J:Finset U)
    (hIT:I⊆T) (hIX:I⊆X) (hJW:J⊆W) (hJZ:J⊆Z) (v:V) (hvX:v∈X) (D:ℝ)
    (havoid:Disjoint (ordinaryPhysicalGraph R S) (ordinaryDeepBlocker T W))
    (hdeg:∀w:V⊕U,((spanningRestriction (ordinaryBoundaryGraph R S T W)
      (ordinaryInnerVertices X Z)).degree w:ℝ)≤D):
    |((R.neighborFinset v∩I).card:ℝ)-2*(J.filter (S v)).card|≤2*D :=by
  let C:=spanningRestriction (ordinaryBoundaryGraph R S T W) (ordinaryInnerVertices X Z)
  have hD:0≤D:=le_trans (by positivity : (0:ℝ)≤(C.degree (Sum.inl v):ℝ)) (hdeg (Sum.inl v))
  by_cases hvT:v∈T
  · have hz:=ordinary_protected_inner_zero R S T W havoid
    have hrim:R.neighborFinset v∩I=∅:=by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxR:(R.Adj v x):=(R.mem_neighborFinset v x).mp (Finset.mem_inter.mp hx).1
      have hxT:x∈T:=hIT (Finset.mem_inter.mp hx).2
      have hh:(spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices T W)).Adj (Sum.inl v) (Sum.inl x):=
        (spanningRestriction_adj _ _ _ _).mpr ⟨hxR,(ordinaryInnerVertices_left T W v).mpr hvT,(ordinaryInnerVertices_left T W x).mpr hxT⟩
      rw [hz] at hh
      exact hh
    have hsp:J.filter (S v)=∅:=by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      have huW:u∈W:=hJW (Finset.mem_filter.mp hu).1
      have huS:S v u:=(Finset.mem_filter.mp hu).2
      have hh:(spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices T W)).Adj (Sum.inl v) (Sum.inr u):=
        (spanningRestriction_adj _ _ _ _).mpr ⟨huS,(ordinaryInnerVertices_left T W v).mpr hvT,(ordinaryInnerVertices_right T W u).mpr huW⟩
      rw [hz] at hh
      exact hh
    simp only [hrim,hsp,Finset.card_empty,Nat.cast_zero,mul_zero,sub_zero,abs_zero]
    positivity
  · let Rim:=R.neighborFinset v∩I
    let Sp:=J.filter (S v)
    have hRim:Rim.image (Sum.inl:V→V⊕U)⊆C.neighborFinset (Sum.inl v):=by
      intro y hy
      obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hy
      have hr:R.Adj v x:=(R.mem_neighborFinset v x).mp (Finset.mem_inter.mp hx).1
      have hxI:x∈I:=(Finset.mem_inter.mp hx).2
      have hb:(ordinaryBoundaryGraph R S T W).Adj (Sum.inl v) (Sum.inl x):=by
        apply (ordinaryBoundaryGraph_adj R S T W _ _).mpr
        refine ⟨hr,Or.inl ⟨?_,(ordinaryInnerVertices_left T W x).mpr (hIT hxI)⟩⟩
        simpa only [ordinaryInnerVertices_left] using hvT
      apply (C.mem_neighborFinset _ _).mpr
      exact (spanningRestriction_adj _ _ _ _).mpr ⟨hb,(ordinaryInnerVertices_left X Z v).mpr hvX,(ordinaryInnerVertices_left X Z x).mpr (hIX hxI)⟩
    have hSp:Sp.image (Sum.inr:U→V⊕U)⊆C.neighborFinset (Sum.inl v):=by
      intro y hy
      obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hy
      have huJ:u∈J:=(Finset.mem_filter.mp hu).1
      have hs:S v u:=(Finset.mem_filter.mp hu).2
      have hb:(ordinaryBoundaryGraph R S T W).Adj (Sum.inl v) (Sum.inr u):=by
        apply (ordinaryBoundaryGraph_adj R S T W _ _).mpr
        refine ⟨hs,Or.inl ⟨?_,(ordinaryInnerVertices_right T W u).mpr (hJW huJ)⟩⟩
        simpa only [ordinaryInnerVertices_left] using hvT
      apply (C.mem_neighborFinset _ _).mpr
      exact (spanningRestriction_adj _ _ _ _).mpr ⟨hb,(ordinaryInnerVertices_left X Z v).mpr hvX,(ordinaryInnerVertices_right X Z u).mpr (hJZ huJ)⟩
    have hRimCard:(Rim.card:ℝ)≤D:=by
      have hh:=Finset.card_le_card hRim
      rw [Finset.card_image_of_injective _ Sum.inl_injective,SimpleGraph.card_neighborFinset_eq_degree] at hh
      have hr:(Rim.card:ℝ)≤(C.degree (Sum.inl v):ℝ):=by exact_mod_cast hh
      exact hr.trans (hdeg (Sum.inl v))
    have hSpCard:(Sp.card:ℝ)≤D:=by
      have hh:=Finset.card_le_card hSp
      rw [Finset.card_image_of_injective _ Sum.inr_injective,SimpleGraph.card_neighborFinset_eq_degree] at hh
      have hs:(Sp.card:ℝ)≤(C.degree (Sum.inl v):ℝ):=by exact_mod_cast hh
      exact hs.trans (hdeg (Sum.inl v))
    have hr0:0≤(Rim.card:ℝ):=by positivity
    have hs0:0≤(Sp.card:ℝ):=by positivity
    change |(Rim.card:ℝ)-2*(Sp.card:ℝ)|≤2*D
    apply abs_le.mpr
    constructor <;> linarith only [hRimCard,hSpCard,hr0,hs0,hD]
end Oberwolfach
