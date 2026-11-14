module

public import Oberwolfach.OrdinaryLocalCycles
public import Oberwolfach.OrdinaryWheelResources
public import Oberwolfach.OrdinaryFactorGraphs
public import Oberwolfach.DisjointCycleLabels

@[expose] public section

/-! A local ordinary cycle factor gives actual wheels at the specified hub.
Rims and spokes remain distinct resources; the deleted rim graph has degree
at most two, and every prescribed spoke occurs exactly once. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {Q F : SimpleGraph V} {T : Finset V} {r : ℕ} {H : V → U → Prop}

def localOrdinaryWheel (u : U) (hH : ∀ v∈T,H v u)
    (C : LocalOrdinaryCycle Q F T r) : OrdinaryWheel Q F H r :=
  ⟨(C.val,u),⟨fun v hv=>hH v (C.property.1 v hv),C.property.2⟩⟩

theorem localOrdinaryWheel_injective (u : U) (hH : ∀ v∈T,H v u) :
    Function.Injective (localOrdinaryWheel (Q:=Q) (F:=F) (r:=r) u hH) := by
  intro C D he
  apply Subtype.ext
  exact congrArg (fun W : OrdinaryWheel Q F H r=>W.val.1) he

def ordinaryWheelRimGraph (M : Finset (OrdinaryWheel Q F H r)) : SimpleGraph V :=
  ⨆ W∈M,ordinaryWheelRim W

theorem ordinaryWheelRimGraph_subhost (M : Finset (OrdinaryWheel Q F H r)) :
    ordinaryWheelRimGraph M≤Q := by
  exact iSup_le (fun W=>iSup_le (fun _=>W.val.1.property))

theorem ordinaryWheelRimGraph_edges (M : Finset (OrdinaryWheel Q F H r)) (e : Sym2 V) :
    e∈(ordinaryWheelRimGraph M).edgeSet ↔ ∃ W∈M,e∈(ordinaryWheelRim W).edgeSet := by
  induction e using Sym2.inductionOn with
  | _ x y => simp only [SimpleGraph.mem_edgeSet,ordinaryWheelRimGraph,SimpleGraph.iSup_adj,exists_prop]

theorem local_ordinary_wheel_resources_disjoint (u : U) (hH : ∀ v∈T,H v u)
    (C D : LocalOrdinaryCycle Q F T r)
    (hCD : Disjoint (localOrdinaryVertices C) (localOrdinaryVertices D)) :
    Disjoint (ordinaryWheelResources (localOrdinaryWheel u hH C))
      (ordinaryWheelResources (localOrdinaryWheel u hH D)) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  cases e with
  | inl e =>
    rw [ordinaryWheelResources_rim] at he hf
    induction e using Sym2.inductionOn with
    | _ x y =>
      have hC : C.val.val.val.Adj x y:=he
      have hD : D.val.val.val.Adj x y:=hf
      exact Finset.disjoint_left.mp hCD
        (Set.mem_toFinset.mpr hC.mem_support_left) (Set.mem_toFinset.mpr hD.mem_support_left)
  | inr vu =>
    rw [ordinaryWheelResources_spoke] at he hf
    exact Finset.disjoint_left.mp hCD
      (Set.mem_toFinset.mpr he.2) (Set.mem_toFinset.mpr hf.2)

theorem local_ordinary_wheel_union (u : U) (hH : ∀ v∈T,H v u)
    (M : Finset (LocalOrdinaryCycle Q F T r)) :
    (M.image (localOrdinaryWheel u hH)).biUnion ordinaryWheelResources=
      (ordinaryWheelRimGraph (M.image (localOrdinaryWheel u hH))).edgeFinset.image Sum.inl ∪
      (M.biUnion localOrdinaryVertices).image (fun v=>Sum.inr (v,u)) := by
  ext e
  cases e with
  | inl e =>
    have hR := ordinaryWheelRimGraph_edges (M.image (localOrdinaryWheel u hH)) e
    simpa only [Finset.mem_biUnion,ordinaryWheelResources_rim,Finset.mem_union,
      Finset.mem_image,Sum.inl.injEq,Sum.inr_ne_inl,and_false,exists_false,or_false,
      SimpleGraph.mem_edgeFinset,exists_eq_right] using hR.symm
  | inr vu =>
    rcases vu with ⟨v,w⟩
    simp only [Finset.mem_biUnion,Finset.mem_image,ordinaryWheelResources_spoke,
      Finset.mem_union,Sum.inl_ne_inr,and_false,exists_false,false_or,
      Sum.inr.injEq,Prod.mk.injEq]
    constructor
    · rintro ⟨_,⟨C,hC,rfl⟩,hu,hv⟩
      exact ⟨v,⟨C,hC,Set.mem_toFinset.mpr hv⟩,rfl,hu⟩
    · rintro ⟨v',⟨C,hC,hv⟩,rfl,hu⟩
      exact ⟨localOrdinaryWheel u hH C,⟨C,hC,rfl⟩,hu,Set.mem_toFinset.mp hv⟩

theorem local_ordinary_wheel_degree (u : U) (hH : ∀ v∈T,H v u)
    (M : Finset (LocalOrdinaryCycle Q F T r))
    (hM : ∀ C∈M,∀ D∈M,C≠D → Disjoint (localOrdinaryVertices C) (localOrdinaryVertices D))
    (v : V) : (ordinaryWheelRimGraph (M.image (localOrdinaryWheel u hH))).degree v≤2 := by
  let N : Finset (OrdinaryCycle Q r):=M.image Subtype.val
  have hN : ∀ C∈N,∀ D∈N,C≠D → Disjoint (ordinaryCycleVertices Q r C) (ordinaryCycleVertices Q r D) := by
    intro C hC D hD hne
    change C∈M.image Subtype.val at hC
    change D∈M.image Subtype.val at hD
    obtain ⟨C',hC',heC⟩ : ∃ C' : LocalOrdinaryCycle Q F T r,C'∈M ∧ C'.val=C := Finset.mem_image.mp hC
    obtain ⟨D',hD',heD⟩ : ∃ D' : LocalOrdinaryCycle Q F T r,D'∈M ∧ D'.val=D := Finset.mem_image.mp hD
    subst C;subst D
    exact hM C' hC' D' hD' (fun h=>hne (congrArg Subtype.val h))
  have he : ordinaryWheelRimGraph (M.image (localOrdinaryWheel u hH))=ordinaryFactorGraph N := by
    ext x y
    simp only [ordinaryWheelRimGraph,ordinaryFactorGraph,SimpleGraph.iSup_adj,N,Finset.mem_image]
    constructor
    · rintro ⟨_,⟨C,hC,rfl⟩,hxy⟩; exact ⟨C.val,⟨C,hC,rfl⟩,hxy⟩
    · rintro ⟨_,⟨C,hC,rfl⟩,hxy⟩; exact ⟨localOrdinaryWheel u hH C,⟨C,hC,rfl⟩,hxy⟩
  rw [he]
  exact ordinaryFactorGraph_degree_le_two N hN v

theorem ordinary_factor_wheels (u : U) (hH : ∀ v∈T,H v u)
    (hfactor : HasResourceDecomposition (localOrdinaryVertices (Q:=Q) (F:=F) (T:=T) (r:=r)) T) :
    ∃ M : Finset (OrdinaryWheel Q F H r),
      (∀ W∈M,∀ Z∈M,W≠Z → Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z)) ∧
      M.biUnion ordinaryWheelResources=(ordinaryWheelRimGraph M).edgeFinset.image Sum.inl ∪
        T.image (fun v=>Sum.inr (v,u)) ∧
      (∀ v,(ordinaryWheelRimGraph M).degree v≤2) ∧
      (∀ W∈M,ordinaryWheelHub W=u) ∧
      (∀ v∈T,∃! W : M,Sum.inr (v,u)∈ordinaryWheelResources W.val) := by
  obtain ⟨N,hN,hcover⟩:=hfactor
  let M:=N.image (localOrdinaryWheel u hH)
  have hM : ∀ W∈M,∀ Z∈M,W≠Z → Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z) := by
    intro W hW Z hZ hne
    obtain ⟨C,hC,rfl⟩:=Finset.mem_image.mp hW
    obtain ⟨D,hD,rfl⟩:=Finset.mem_image.mp hZ
    apply local_ordinary_wheel_resources_disjoint
    exact hN C hC D hD (fun h=>hne (congrArg (localOrdinaryWheel u hH) h))
  have hunion : M.biUnion ordinaryWheelResources=(ordinaryWheelRimGraph M).edgeFinset.image Sum.inl ∪
      T.image (fun v=>Sum.inr (v,u)) := by
    simpa only [hcover] using local_ordinary_wheel_union u hH N
  refine ⟨M,hM,hunion,local_ordinary_wheel_degree u hH N hN,?_,?_⟩
  · intro W hW
    obtain ⟨C,hC,rfl⟩:=Finset.mem_image.mp hW
    rfl
  · intro v hv
    apply resource_factor_vertex_unique ordinaryWheelResources M hM
    rw [hunion]
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩)

end Oberwolfach
