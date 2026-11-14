module

public import Oberwolfach.OrdinaryBoundarySupportExact
public import Oberwolfach.PhysicalBoundaryFullClassAfterPacking
public import Oberwolfach.HubSelectedClassGeometry

@[expose] public section
/-! Actual classes after an approximate packing and cleanup remain close to
their sampled classes, with no further random sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]

theorem ordinary_boundary_factor_classes_after_packing_outside_degree
    (Q Q':SimpleGraph V) (H H':V→U→Prop) (X:Finset V) (Z:Finset U)
    (C D:SimpleGraph (V⊕U)) (σ:Sym2 (V⊕U)→Bool) (L:ℝ)
    (hCR:Disjoint C (retainedGraph (ordinaryBoundaryGraph Q H X Z) σ))
    (hphys:ordinaryBoundaryGraph Q' H' X Z=((ordinaryBoundaryGraph Q H X Z\C)\D))
    (hLhub:∀j:{u:U // u∉Z},((((ordinaryBoundaryGraph Q H X Z)\retainedGraph (ordinaryBoundaryGraph Q H X Z) σ)\C).degree (Sum.inr j.val):ℝ)+
      (D.degree (Sum.inr j.val):ℝ)≤L)
    (hLrim:∀i:{v:V // v∉X},((((ordinaryBoundaryGraph Q H X Z)\retainedGraph (ordinaryBoundaryGraph Q H X Z) σ)\C).degree (Sum.inl i.val):ℝ)+
      (D.degree (Sum.inl i.val):ℝ)≤L):
    (∀j:{u:U // u∉Z},
      (((((ordinaryBoundaryHubSet H Z X j).filter (fun v=>σ (hubSpokeCoin j.val v)=true))\
        ordinaryBoundaryHubSet H' Z X j).card+
        ((ordinaryBoundaryHubSet H' Z X j)\((ordinaryBoundaryHubSet H Z X j).filter
          (fun v=>σ (hubSpokeCoin j.val v)=true))).card:ℕ):ℝ)≤L) ∧
    (∀i:{v:V // v∉X},
      let S:=(ordinaryBoundaryRimSet Q X i).image Sum.inl∪(ordinaryBoundaryRowSet H X Z i).image Sum.inr;
      let A:=(ordinaryBoundaryRimSet Q' X i).image Sum.inl∪(ordinaryBoundaryRowSet H' X Z i).image Sum.inr;
      (((S.filter (fun w=>σ (physicalIncidentCoin (Sum.inl i.val) w)=true)\A).card+
        (A\S.filter (fun w=>σ (physicalIncidentCoin (Sum.inl i.val) w)=true)).card:ℕ):ℝ)≤L):=by
  let G:=ordinaryBoundaryGraph Q H X Z
  let G':=(G\C)\D
  have hroot (i:{u:U // u∉Z}⊕{v:V // v∉X}):
      ordinaryBoundaryPhysicalSupports Q' H' X Z i=G'.neighborFinset (ordinaryBoundaryPhysicalRoot X Z i):=by
    rw [ordinary_boundary_supports_eq_neighbors]
    ext w
    simp only [SimpleGraph.mem_neighborFinset]
    change (ordinaryBoundaryGraph Q' H' X Z).Adj _ _ ↔ ((G\C)\D).Adj _ _
    rw [hphys]
  have hroot0 (i:{u:U // u∉Z}⊕{v:V // v∉X}):
      ordinaryBoundaryPhysicalSupports Q H X Z i=G.neighborFinset (ordinaryBoundaryPhysicalRoot X Z i):=
    ordinary_boundary_supports_eq_neighbors Q H X Z i
  refine ⟨?_,?_⟩
  · intro j
    let T:=ordinaryBoundaryHubSet H Z X j
    let Y:=ordinaryBoundaryHubSet H' Z X j
    have hbase (v:V):v∈T↔G.Adj (Sum.inr j.val) (Sum.inl v):=by
      have hh:=hroot0 (Sum.inl j)
      have hh':Sum.inl v∈ordinaryBoundaryPhysicalSupports Q H X Z (Sum.inl j)↔
          Sum.inl v∈G.neighborFinset (ordinaryBoundaryPhysicalRoot X Z (Sum.inl j)):=by rw [hh]
      simpa [ordinaryBoundaryPhysicalSupports,ordinaryBoundaryPhysicalRoot,SimpleGraph.mem_neighborFinset] using hh'
    have hnew (v:V):v∈Y↔G'.Adj (Sum.inr j.val) (Sum.inl v):=by
      have hh:=hroot (Sum.inl j)
      have hh':Sum.inl v∈ordinaryBoundaryPhysicalSupports Q' H' X Z (Sum.inl j)↔
          Sum.inl v∈G'.neighborFinset (ordinaryBoundaryPhysicalRoot X Z (Sum.inl j)):=by rw [hh]
      simpa [ordinaryBoundaryPhysicalSupports,ordinaryBoundaryPhysicalRoot,SimpleGraph.mem_neighborFinset] using hh'
    have hfilter:T.filter (fun v=>G'.Adj (Sum.inl v) (Sum.inr j.val))=Y:=by
      ext v
      simp only [Finset.mem_filter,hnew]
      constructor
      · rintro ⟨_,h⟩;exact h.symm
      · intro h
        have hh:G.Adj (Sum.inr j.val) (Sum.inl v):=(show G'≤G from sdiff_le.trans sdiff_le) h
        exact ⟨(hbase v).mpr hh,h.symm⟩
    have hh:=physical_hub_boundary_class_after_packing j.val T G C D σ
      (fun v hv=>(hbase v).mp hv) hCR
    rw [hfilter,changed_card_eq_differences] at hh
    have hc:= (Nat.cast_le (α:=ℝ)).mpr hh
    push_cast at hc
    have hl:(((G\retainedGraph G σ)\C).degree (Sum.inr j.val):ℝ)+D.degree (Sum.inr j.val)≤L:=by
      convert hLhub j using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    dsimp only [T,Y] at hc
    push_cast
    linarith only [hc,hl]
  · intro i S A
    have hS:S=G.neighborFinset (Sum.inl i.val):=by
      simpa [S,ordinaryBoundaryPhysicalSupports,ordinaryBoundaryPhysicalRoot] using hroot0 (Sum.inr i)
    have hA:A=G'.neighborFinset (Sum.inl i.val):=by
      simpa [A,ordinaryBoundaryPhysicalSupports,ordinaryBoundaryPhysicalRoot] using hroot (Sum.inr i)
    have hf:(G.neighborFinset (Sum.inl i.val)).filter
        (fun w=>σ (physicalIncidentCoin (Sum.inl i.val) w)=true)=
        (retainedGraph G σ).neighborFinset (Sum.inl i.val):=by
      ext w
      simp [physicalIncidentCoin,retainedGraph,SimpleGraph.mem_neighborFinset]
    have hh:=physical_boundary_neighborhood_after_packing (Sum.inl i.val) G C D σ hCR
    rw [changed_card_eq_differences] at hh
    have hc:((((G'.neighborFinset (Sum.inl i.val))\(retainedGraph G σ).neighborFinset (Sum.inl i.val)).card+
        (((retainedGraph G σ).neighborFinset (Sum.inl i.val))\G'.neighborFinset (Sum.inl i.val)).card:ℕ):ℝ)≤
        (((G\retainedGraph G σ)\C).degree (Sum.inl i.val):ℝ)+D.degree (Sum.inl i.val):=by exact_mod_cast hh
    rw [hS,hA,hf]
    have hl:(((G\retainedGraph G σ)\C).degree (Sum.inl i.val):ℝ)+D.degree (Sum.inl i.val)≤L:=by
      convert hLrim i using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    push_cast at hc ⊢
    linarith only [hc,hl]
end Oberwolfach
