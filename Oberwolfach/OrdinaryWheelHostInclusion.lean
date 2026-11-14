module

public import Oberwolfach.OrdinaryFactorWheels

@[expose] public section

/-! A wheel in a remaining rim graph is a wheel in the original host.
The physical edge set is preserved, so the transport does not change
multiplicities, forbidden-pair restrictions, or spoke coverage. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {P Q F : SimpleGraph V} {H : V→U→Prop} {r : ℕ}

def ordinaryWheelInclude (hQP : Q≤P) (W : OrdinaryWheel Q F H r) : OrdinaryWheel P F H r :=
  ⟨(⟨W.val.1.val,W.val.1.property.trans hQP⟩,W.val.2),W.property⟩

theorem ordinaryWheelInclude_resources (hQP : Q≤P) (W : OrdinaryWheel Q F H r) :
    ordinaryWheelResources (ordinaryWheelInclude hQP W)=ordinaryWheelResources W := rfl

theorem ordinaryWheelInclude_rimGraph (hQP : Q≤P) (M : Finset (OrdinaryWheel Q F H r)) :
    ordinaryWheelRimGraph (M.image (ordinaryWheelInclude hQP))=ordinaryWheelRimGraph M := by
  ext x y
  simp only [ordinaryWheelRimGraph,SimpleGraph.iSup_adj,Finset.mem_image]
  constructor
  · rintro ⟨_,⟨W,hW,rfl⟩,hxy⟩;exact ⟨W,hW,hxy⟩
  · rintro ⟨W,hW,hxy⟩;exact ⟨ordinaryWheelInclude hQP W,⟨W,hW,rfl⟩,hxy⟩

theorem ordinaryWheelInclude_union (hQP : Q≤P) (M : Finset (OrdinaryWheel Q F H r)) :
    (M.image (ordinaryWheelInclude hQP)).biUnion ordinaryWheelResources=M.biUnion ordinaryWheelResources := by
  ext e
  simp only [Finset.mem_biUnion,Finset.mem_image]
  constructor
  · rintro ⟨_,⟨W,hW,rfl⟩,he⟩;exact ⟨W,hW,he⟩
  · rintro ⟨W,hW,he⟩;exact ⟨ordinaryWheelInclude hQP W,⟨W,hW,rfl⟩,he⟩

theorem ordinary_factor_wheels_avoiding (D : SimpleGraph V) (T : Finset V)
    (u : U) (hH : ∀ v∈T,H v u)
    (hfactor : HasResourceDecomposition (localOrdinaryVertices (Q:=Q\D) (F:=F) (T:=T) (r:=r)) T) :
    ∃ M : Finset (OrdinaryWheel Q F H r),
      (∀ W∈M,∀ Z∈M,W≠Z → Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z)) ∧
      M.biUnion ordinaryWheelResources=(ordinaryWheelRimGraph M).edgeFinset.image Sum.inl ∪
        T.image (fun v=>Sum.inr (v,u)) ∧
      (∀ v,(ordinaryWheelRimGraph M).degree v≤2) ∧
      (∀ W∈M,ordinaryWheelHub W=u) ∧ Disjoint (ordinaryWheelRimGraph M) D := by
  obtain ⟨M,hM,hunion,hdeg,hhub,_⟩:=ordinary_factor_wheels (Q:=Q\D) u hH hfactor
  let f:=ordinaryWheelInclude (P:=Q) (Q:=Q\D) (F:=F) (H:=H) (r:=r) sdiff_le
  have hgraph : ordinaryWheelRimGraph (M.image f)=ordinaryWheelRimGraph M:=ordinaryWheelInclude_rimGraph sdiff_le M
  refine ⟨M.image f,?_,?_,?_,?_,?_⟩
  · intro W hW Z hZ hne
    obtain ⟨W',hW',rfl⟩:=Finset.mem_image.mp hW
    obtain ⟨Z',hZ',rfl⟩:=Finset.mem_image.mp hZ
    exact hM W' hW' Z' hZ' (fun h=>hne (congrArg f h))
  · rw [ordinaryWheelInclude_union,hgraph]
    exact hunion
  · intro v
    rw [hgraph]
    exact hdeg v
  · intro W hW
    obtain ⟨W',hW',rfl⟩:=Finset.mem_image.mp hW
    exact hhub W' hW'
  · rw [hgraph]
    apply disjoint_iff_inf_le.mpr
    intro x y hxy
    exact ((ordinaryWheelRimGraph_subhost M hxy.1).2 hxy.2).elim

end Oberwolfach
