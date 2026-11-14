module

public import Oberwolfach.MarkedConfigurationsAfterPhysicalDeletion

@[expose] public section
/-! Local configurations are monotone under inclusion of the same typed rims
and spokes, retaining the vertex tuples and all root omissions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_local_configurations_rim_inclusion
    (r:ℕ) (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (βC βP:ℝ)
    (σ τ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hrim:∀ mark x y,markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1→
      markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1)
    (hc:MarkedLocalConfigurationsWithSpokes r P π d Finset.univ βC βP σ H):
    MarkedLocalConfigurationsWithSpokes r P π d Finset.univ βC βP τ H:=by
  constructor
  · intro u
    let T₀:=Finset.univ.filter (H false · u)
    let TK:=Finset.univ.filter (H true · u)
    let F : {C:DenseMarkedBaseFamily P π (3*d) (r+4) T₀ TK //
        MarkedBaseRims P π (3*d) (r+4) (fun e=>σ (Sum.inl e)) C.val} →
      {C:DenseMarkedBaseFamily P π (3*d) (r+4) T₀ TK //
        MarkedBaseRims P π (3*d) (r+4) (fun e=>τ (Sum.inl e)) C.val} := fun C=>
      ⟨C.val,⟨fun i=>hrim false _ _ (C.property.1 i),hrim true _ _ C.property.2⟩⟩
    have hf:Function.Injective F:=by
      intro C D h
      have hh:=congrArg (fun z=>z.val) h
      exact Subtype.ext hh
    have hn:=Fintype.card_le_of_injective F hf
    exact (hc.1 u).trans (by exact_mod_cast hn)
  · intro u j v v' hv
    let T₀:=Finset.univ.filter (H false · u)
    let TK:=Finset.univ.filter (H true · u)
    let F : {C:DenseRootMarkedPathFamily P π (3*d) (r+3) j T₀ TK v v' //
        MarkedPathRims P π (3*d) (r+3) j v v' (fun e=>σ (Sum.inl e)) C.val} →
      {C:DenseRootMarkedPathFamily P π (3*d) (r+3) j T₀ TK v v' //
        MarkedPathRims P π (3*d) (r+3) j v v' (fun e=>τ (Sum.inl e)) C.val} := fun C=>
      ⟨C.val,fun i=>hrim _ _ _ (C.property i)⟩
    have hf:Function.Injective F:=by
      intro C D h
      have hh:=congrArg (fun z=>z.val) h
      exact Subtype.ext hh
    have hn:=Fintype.card_le_of_injective F hf
    exact (hc.2 u j v v' hv).trans (by exact_mod_cast hn)

theorem marked_local_configurations_spoke_inclusion
    (r:ℕ) (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (βC βP:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (hH:∀ b x u,H b x u→H' b x u)
    (hc:MarkedLocalConfigurationsWithSpokes r P π d Finset.univ βC βP σ H):
    MarkedLocalConfigurationsWithSpokes r P π d Finset.univ βC βP σ H':=by
  have hz (b:Bool) (u:U):
      (((Finset.univ.filter (H b · u))\(Finset.univ.filter (H' b · u))).card:ℝ)≤
        (0:ℝ)*(Finset.univ:Finset V).card:=by
    have hsub:(Finset.univ.filter (H b · u))⊆Finset.univ.filter (H' b · u):=by
      intro x hx
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hx ⊢
      exact hH b x u hx
    rw [Finset.sdiff_eq_empty_iff_subset.mpr hsub]
    simp
  have hh:=markedLocalPhysicalCounts_class_changes r (3*d) P π Finset.univ
    (fun u=>Finset.univ.filter (H false · u)) (fun u=>Finset.univ.filter (H true · u))
    (fun u=>Finset.univ.filter (H' false · u)) (fun u=>Finset.univ.filter (H' true · u))
    (fun _=>Finset.filter_subset _ _) (fun _=>Finset.filter_subset _ _)
    (fun _=>Finset.filter_subset _ _) (fun _=>Finset.filter_subset _ _)
    βC βP 0 (hz false) (hz true) (fun e=>σ (Sum.inl e)) hc
  unfold MarkedLocalConfigurationsWithSpokes
  simpa only [mul_zero,sub_zero] using hh
end Oberwolfach
