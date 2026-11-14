module

public import Oberwolfach.OrdinaryCleanupParentProfiles
public import Oberwolfach.OrdinaryCleanupPostFacts
public import Oberwolfach.OrdinaryPhysicalCleanupEdit
public import Oberwolfach.OrdinaryPhysicalEditToTypedChanges
public import Oberwolfach.OrdinaryBoundaryExtensionStability

@[expose] public section
/-! The unreserved packing avoids the entire protected inner pair. Thus the
inner endpoint-extension counts retain the full parent lower bound, losing
only the sparse cleanup cost and no fresh-sampling factor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_inner_counts_after_packing_cleanup
    (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d r:ℕ)
    (X:Finset V) (Z:Finset U) (pR pH density tR tH L βe βh t ν:ℝ)
    (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (R:SimpleGraph (V⊕U))
    (profile:OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH L βe βh s j raw)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card)
    (M:OrdinaryUnreservedPackingData Q F H X Z R r t):
    let Qpost:=ordinaryPackingPostRim Q F H X Z R r t M;
    let Hpost:=ordinaryPackingPostSpokes Q F H X Z R r t M;
    let C:=ordinaryPackingUsedGraph Q F H X Z R r t M;
    ∀(K:OrdinaryOutsideCleanupData Qpost F Hpost X Z C r ν),
    let Qfinal:=ordinaryCleanupPostRim Qpost F Hpost X Z C r ν K;
    let Hfinal:=ordinaryCleanupPostSpokes Qpost F Hpost X Z C r ν K;
    ∀u∈Z,∀a∈X,∀c∈X,βe*Fintype.card (V⊕U)-3*ν≤
      (((X.filter (fun v=>Hfinal v u))∩Qfinal.neighborFinset a∩Qfinal.neighborFinset c).card:ℝ):=by
  intro Qpost Hpost C K Qfinal Hfinal
  have hm:=ordinary_packing_post_facts Q F H X Z R r t M hbal hdiv
  have hparent:=ordinary_boundary_parent_common_of_min_degree P X density profile.parent_min_degree
  have hpairs:=ordinary_boundary_parent_extensions_from_common_sample P Q H π d X pR pH (2*density-1)
    tR L βe profile.rim_nonneg profile.rim_le_one profile.spoke_nonneg (by linarith [profile.density_large])
    s j raw profile.spoke_probability profile.rows hparent profile.rim_edit profile.spoke_column_edit profile.extension_margin
  have hkeep {x y:V⊕U} (hx:x∈ordinaryInnerVertices X Z) (hy:y∈ordinaryInnerVertices X Z)
      (hxy:(ordinaryPhysicalGraph Q H).Adj x y):(ordinaryPhysicalGraph Qpost Hpost).Adj x y:=by
    have hi:(spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z)).Adj x y:=
      (spanningRestriction_adj _ _ _ _).mpr ⟨hxy,hx,hy⟩
    have hn:¬C.Adj x y:=by
      intro hc
      exact (disjoint_iff_inf_le.mp hm.inner_avoided) ⟨hc,hi⟩
    rw [hm.exact_remainder]
    exact ⟨hxy,hn⟩
  have hpost (u:U) (hu:u∈Z) (a:V) (ha:a∈X) (c:V) (hc:c∈X):
      βe*Fintype.card (V⊕U)≤
        (((X.filter (fun v=>Hpost v u))∩Qpost.neighborFinset a∩Qpost.neighborFinset c).card:ℝ):=by
    have hsub:X.filter (fun v=>Q.Adj a v∧Q.Adj v c∧H v u)⊆
        (X.filter (fun v=>Hpost v u))∩Qpost.neighborFinset a∩Qpost.neighborFinset c:=by
      intro v hv
      obtain ⟨hvX,hav,hvc,hvu⟩:=Finset.mem_filter.mp hv
      have hva:Sum.inl a∈ordinaryInnerVertices X Z:=(ordinaryInnerVertices_left X Z a).2 ha
      have hvv:Sum.inl v∈ordinaryInnerVertices X Z:=(ordinaryInnerVertices_left X Z v).2 hvX
      have hvc':Sum.inl c∈ordinaryInnerVertices X Z:=(ordinaryInnerVertices_left X Z c).2 hc
      have hvu':Sum.inr u∈ordinaryInnerVertices X Z:=(ordinaryInnerVertices_right X Z u).2 hu
      have hpav:Qpost.Adj a v:=hkeep hva hvv hav
      have hpvc:Qpost.Adj v c:=hkeep hvv hvc' hvc
      have hpvu:Hpost v u:=hkeep hvv hvu' hvu
      simp only [Finset.mem_inter,Finset.mem_filter,SimpleGraph.mem_neighborFinset]
      exact ⟨⟨⟨hvX,hpvu⟩,hpav⟩,hpvc.symm⟩
    have hcard:=Finset.card_le_card hsub
    have hreal:((X.filter (fun v=>Q.Adj a v∧Q.Adj v c∧H v u)).card:ℝ)≤
      (((X.filter (fun v=>Hpost v u))∩Qpost.neighborFinset a∩Qpost.neighborFinset c).card:ℝ):=by exact_mod_cast hcard
    exact (hpairs a c u).trans hreal
  have hedit:=ordinary_physical_cleanup_edit Qpost (wheelFamilyRim K.wheels) Hpost (wheelFamilySpokes K.wheels) ν K.degree
  have ht:=ordinary_physical_edit_to_typed_changes Qpost Qfinal Hpost Hfinal ν hedit
  intro u hu a ha c hc
  have hst:=ordinary_boundary_extension_count_stability Qpost Qfinal Hpost Hfinal X a c u ν
    (ht.1 a) (ht.1 c) (ht.2.2 u)
  have he (G:SimpleGraph V) (T:V→U→Prop):
      X.filter (fun v=>G.Adj a v∧G.Adj v c∧T v u)=
      (X.filter (fun v=>T v u))∩G.neighborFinset a∩G.neighborFinset c:=by
    ext v
    simp only [Finset.mem_filter,Finset.mem_inter,SimpleGraph.mem_neighborFinset]
    have hg:=G.adj_comm v c
    tauto
  rw [he,he] at hst
  have hst':=(abs_le.mp hst).2
  have hp:=hpost u hu a ha c hc
  linarith only [hp,hst']
end Oberwolfach
