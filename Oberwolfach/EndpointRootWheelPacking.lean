module

public import Oberwolfach.EndpointRootWheels
public import Oberwolfach.OrdinaryWheelFamilies
public import Oberwolfach.GraphSelectionDegrees
public import Oberwolfach.DisjointCycleLabels

@[expose] public section

/-! A vertex-disjoint endpoint-triangle factor completes all prescribed
edges at one external row root. Physical wheel edges are disjoint even
though all rim triangles contain that root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem endpoint_factor_root_wheel_packing (Q H F : SimpleGraph V) (A B S T : Finset V)
    (hAB : Disjoint A B) (hSA : S⊆A) (hTB : T⊆B) (x : V)
    (hS : ∀ v∈S,Q.Adj x v ∧ ¬F.Adj x v) (hT : ∀ u∈T,H.Adj x u)
    (M : Finset (EndpointTriangle (endpointHostGraph Q H A B) F S T))
    (hM : ∀ C∈M,∀ D∈M,C≠D → Disjoint (endpointTriangleVertices C) (endpointTriangleVertices D))
    (hcover : M.biUnion endpointTriangleVertices=S∪T) :
    ∃ W : M→OrdinaryWheel Q F H.Adj 3,
      (∀ C,ordinaryWheelHub (W C)=endpointTriangleIndex C.val ∧
        (ordinaryWheelRim (W C)).support.toFinset=insert x (C.val.val∩S)) ∧
      (∀ C D,C≠D → Disjoint (ordinaryWheelResources (W C)) (ordinaryWheelResources (W D))) ∧
      (∀ v∈S,∃! C,Sum.inl s(x,v)∈ordinaryWheelResources (W C)) ∧
      (∀ u∈T,∃! C,Sum.inr (x,u)∈ordinaryWheelResources (W C)) ∧
      (∀ v,v≠x → (wheelFamilyRim W).degree v≤2) := by
  have hex (C : M):=endpoint_triangle_root_wheel Q H F A B S T hAB hSA hTB x hS hT C.val
  let W : M→OrdinaryWheel Q F H.Adj 3:=fun C=>Classical.choose (hex C)
  have hW (C : M) : ordinaryWheelHub (W C)=endpointTriangleIndex C.val ∧
      (ordinaryWheelRim (W C)).support.toFinset=insert x (C.val.val∩S):=Classical.choose_spec (hex C)
  have hsupp (C : M) (v : V) : v∈(ordinaryWheelRim (W C)).support ↔ v=x ∨ v∈C.val.val∩S := by
    rw [←Set.mem_toFinset,(hW C).2,Finset.mem_insert]
  have hshare (C D : M) (hne : C≠D) (v : V) (hv : v∈C.val.val) (hv' : v∈D.val.val) : False :=
    Finset.disjoint_left.mp (hM C.val C.property D.val D.property (fun h=>hne (Subtype.ext h))) hv hv'
  have hidx (C D : M) (hne : C≠D) : endpointTriangleIndex C.val≠endpointTriangleIndex D.val := by
    intro he
    exact hshare C D hne _ (endpointTriangleIndex_mem C.val).1 (he.symm ▸ (endpointTriangleIndex_mem D.val).1)
  have hdisj (C D : M) (hne : C≠D) :
      Disjoint (ordinaryWheelResources (W C)) (ordinaryWheelResources (W D)) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    cases e with
    | inl e =>
      rw [ordinaryWheelResources_rim] at he hf
      induction e using Sym2.ind with
      | _ v w =>
        have hcv : v∈(ordinaryWheelRim (W C)).support:=he.mem_support_left
        have hdv : v∈(ordinaryWheelRim (W D)).support:=hf.mem_support_left
        have hcw : w∈(ordinaryWheelRim (W C)).support:=he.mem_support_right
        have hdw : w∈(ordinaryWheelRim (W D)).support:=hf.mem_support_right
        by_cases hvx : v=x
        · have hwx : w≠x:=fun h=>he.ne (hvx.trans h.symm)
          exact hshare C D hne w
            (Finset.mem_inter.mp ((hsupp C w).mp hcw |>.resolve_left hwx)).1
            (Finset.mem_inter.mp ((hsupp D w).mp hdw |>.resolve_left hwx)).1
        · exact hshare C D hne v
            (Finset.mem_inter.mp ((hsupp C v).mp hcv |>.resolve_left hvx)).1
            (Finset.mem_inter.mp ((hsupp D v).mp hdv |>.resolve_left hvx)).1
    | inr vu =>
      rw [ordinaryWheelResources_spoke] at he hf
      exact hidx C D hne ((hW C).1.symm.trans (he.1.trans (hf.1.symm.trans (hW D).1)))
  have hcy (C : M) : IsEmbeddedCycle (ordinaryWheelRim (W C)) 3 := (W C).val.1.val.property
  have hrim (C : M) (v : V) (hv : v∈S) :
      Sum.inl s(x,v)∈ordinaryWheelResources (W C) ↔ v∈C.val.val := by
    rw [ordinaryWheelResources_rim,SimpleGraph.mem_edgeSet,(hcy C).triangle_adj,hsupp,hsupp]
    have hne : x≠v:=(hS v hv).1.ne
    simp only [or_true,Finset.mem_inter,true_or,true_and,hv,and_true]
    tauto
  have hspoke (C : M) (u : V) (hu : u∈T) :
      Sum.inr (x,u)∈ordinaryWheelResources (W C) ↔ u∈C.val.val := by
    rw [ordinaryWheelResources_spoke,(hW C).1,hsupp]
    simp only [true_or,and_true]
    constructor
    · intro he;exact he ▸ (endpointTriangleIndex_mem C.val).1
    · intro huC
      have hh : u∈C.val.val∩T:=Finset.mem_inter.mpr ⟨huC,hu⟩
      rw [endpointTriangleIndex_spec,Finset.mem_singleton] at hh
      exact hh.symm
  refine ⟨W,hW,hdisj,?_,?_,?_⟩
  · intro v hv
    have hh:=resource_factor_vertex_unique endpointTriangleVertices M hM v
      (hcover ▸ Finset.mem_union_left T hv)
    obtain ⟨C,hC,huniq⟩:=hh
    refine ⟨C,(hrim C v hv).mpr hC,?_⟩
    intro D hD;exact huniq D ((hrim D v hv).mp hD)
  · intro u hu
    have hh:=resource_factor_vertex_unique endpointTriangleVertices M hM u
      (hcover ▸ Finset.mem_union_right S hu)
    obtain ⟨C,hC,huniq⟩:=hh
    refine ⟨C,(hspoke C u hu).mpr hC,?_⟩
    intro D hD;exact huniq D ((hspoke D u hu).mp hD)
  · intro v hvx
    have hc : (Finset.univ.filter (fun C : M=>∃ w∈(Finset.univ:Finset V),
        (ordinaryWheelRim (W C)).Adj v w)).card≤1 := by
      apply Finset.card_le_one.mpr
      intro C hC D hD
      by_contra hne
      obtain ⟨w,_,hw⟩:=(Finset.mem_filter.mp hC).2
      obtain ⟨z,_,hz⟩:=(Finset.mem_filter.mp hD).2
      exact hshare C D hne v
        (Finset.mem_inter.mp ((hsupp C v).mp hw.mem_support_left |>.resolve_left hvx)).1
        (Finset.mem_inter.mp ((hsupp D v).mp hz.mem_support_left |>.resolve_left hvx)).1
    have hh:=graph_iSup_local_degree_bound (fun C : M=>ordinaryWheelRim (W C)) Finset.univ v 2 (by
      intro C;rcases (hcy C).degree_zero_or_two v with h|h <;> omega)
    simp only [Finset.inter_univ,SimpleGraph.card_neighborFinset_eq_degree] at hh
    exact hh.trans (by omega)

end Oberwolfach
