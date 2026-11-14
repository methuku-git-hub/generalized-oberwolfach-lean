module

public import Oberwolfach.TriangleFactorHubTrade

@[expose] public section
/-! The physical factor pair gives the ordinary hub switch for every cycle
length; the root condition prevents rim edges inside the old root set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_separated_factor_pair_hub_trade (G:SimpleGraph V) (H:V→U→Prop)
    (A Z:Finset V) (hAZ:Disjoint A Z) (u u':U) (hu:u≠u')
    (r:ℕ) (M₁ M₀:Finset (OrdinaryCycle G r))
    (hp₁:∀ C∈M₁,∀ E∈M₁,C≠E→Disjoint (ordinaryCycleVertices G r C) (ordinaryCycleVertices G r E))
    (hc₁:M₁.biUnion (ordinaryCycleVertices G r)=A∪Z)
    (hp₀:∀ C∈M₀,∀ E∈M₀,C≠E→Disjoint (ordinaryCycleVertices G r C) (ordinaryCycleVertices G r E))
    (hc₀:M₀.biUnion (ordinaryCycleVertices G r)=A)
    (hcross:∀ C∈M₁,∀ E∈M₀,Disjoint C.val.val.edgeFinset E.val.val.edgeFinset)
    (hroot:∀ C∈M₁,(ordinaryCycleVertices G r C∩Z).card≤1)
    (hH:∀ v∈A∪Z,H v u∧H v u'):
    ∃ R:SimpleGraph V,
    let Splus:V→U→Prop:=fun v z=>(v∈A∪Z∧z=u)∨(v∈A∧z=u')
    let Sminus:V→U→Prop:=fun v z=>(v∈A∪Z∧z=u')∨(v∈A∧z=u)
    HasOrdinaryWheelDecomposition R Splus r ∧ HasOrdinaryWheelDecomposition R Sminus r ∧
    HasResourceDecomposition (ordinaryWheelResources (P:=G) (F:=⊥) (Hbase:=H) (r:=r)) (ordinaryHostResources R Splus) ∧
    HasResourceDecomposition (ordinaryWheelResources (P:=G) (F:=⊥) (Hbase:=H) (r:=r)) (ordinaryHostResources R Sminus) ∧
    R≤G ∧ (∀ v w,R.Adj v w→v∈A∪Z ∧ w∈A∪Z) ∧ (∀ v w,v∈Z→w∈Z→¬R.Adj v w) ∧ (∀ v z,Splus v z→H v z) ∧ (∀ v z,Sminus v z→H v z) ∧
    (∀ e:Sym2 V⊕(V×U),
      (if e∈ordinaryHostResources R Splus then (1:ℤ) else 0)-
      (if e∈ordinaryHostResources R Sminus then 1 else 0)=
      (if e∈Z.image (fun v=>Sum.inr (v,u)) then 1 else 0)-
      (if e∈Z.image (fun v=>Sum.inr (v,u')) then 1 else 0)):=by
  let f:OrdinaryCycle G r↪LocalOrdinaryCycle G ⊥ Finset.univ r:=
    ⟨fun C=>⟨C,by simp⟩,fun C D h=>congrArg Subtype.val h⟩
  let D₀:=M₀.image f
  let D₁:=M₁.image f
  have hverts (C:OrdinaryCycle G r):localOrdinaryVertices (f C)=ordinaryCycleVertices G r C:=rfl
  have hpack (M:Finset (OrdinaryCycle G r))
      (hM:∀ C∈M,∀ D∈M,C≠D→Disjoint (ordinaryCycleVertices G r C) (ordinaryCycleVertices G r D)):
      ∀ C∈M.image f,∀ D∈M.image f,C≠D→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices D):=by
    intro C hC D hD hne
    obtain ⟨C₀,hC₀,rfl⟩:=Finset.mem_image.mp hC
    obtain ⟨D₀,hD₀,rfl⟩:=Finset.mem_image.mp hD
    simpa only [hverts] using hM C₀ hC₀ D₀ hD₀ (fun h=>hne (congrArg f h))
  have hcover (M:Finset (OrdinaryCycle G r)):
      (M.image f).biUnion localOrdinaryVertices=M.biUnion (ordinaryCycleVertices G r):=by
    ext v
    simp only [Finset.mem_biUnion,Finset.mem_image]
    constructor
    · rintro ⟨_,⟨C,hC,rfl⟩,hv⟩;exact ⟨C,hC,by simpa only [hverts] using hv⟩
    · rintro ⟨C,hC,hv⟩;exact ⟨f C,⟨C,hC,rfl⟩,by simpa only [hverts] using hv⟩
  have hD₀:(∀ C∈D₀,∀ D∈D₀,C≠D→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices D)) ∧
      D₀.biUnion localOrdinaryVertices=A:=⟨hpack M₀ hp₀,(hcover M₀).trans hc₀⟩
  have hD₁:(∀ C∈D₁,∀ D∈D₁,C≠D→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices D)) ∧
      D₁.biUnion localOrdinaryVertices=A∪Z:=⟨hpack M₁ hp₁,(hcover M₁).trans hc₁⟩
  have hdis:Disjoint (localOrdinaryFactorGraph D₀) (localOrdinaryFactorGraph D₁):=by
    apply disjoint_iff_inf_le.mpr
    intro x y hxy
    obtain ⟨C,hC,hCxy⟩:=(localOrdinaryFactorGraph_adj D₀ x y).mp hxy.1
    obtain ⟨D,hD,hDxy⟩:=(localOrdinaryFactorGraph_adj D₁ x y).mp hxy.2
    change C∈M₀.image f at hC
    change D∈M₁.image f at hD
    obtain ⟨C₀,hC₀,rfl⟩:=Finset.mem_image.mp hC
    obtain ⟨D₀,hD₀,rfl⟩:=Finset.mem_image.mp hD
    change C₀.val.val.Adj x y at hCxy
    change D₀.val.val.Adj x y at hDxy
    have heD:s(x,y)∈D₀.val.val.edgeFinset:=SimpleGraph.mem_edgeFinset.mpr hDxy
    have heC:s(x,y)∈C₀.val.val.edgeFinset:=SimpleGraph.mem_edgeFinset.mpr hCxy
    exact Finset.disjoint_left.mp (hcross D₀ hD₀ C₀ hC₀) heD heC
  have hsupp:∀ v w,(localOrdinaryFactorGraph D₁⊔localOrdinaryFactorGraph D₀).Adj v w→v∈A∪Z ∧ w∈A∪Z:=by
    intro v w hadj
    simp only [SimpleGraph.sup_adj] at hadj
    rcases hadj with hadj|hadj
    · obtain ⟨C,hC,hCvw⟩:=(localOrdinaryFactorGraph_adj D₁ v w).mp hadj
      constructor <;> rw [←hD₁.2]
      · exact Finset.mem_biUnion.mpr ⟨C,hC,Set.mem_toFinset.mpr hCvw.mem_support_left⟩
      · exact Finset.mem_biUnion.mpr ⟨C,hC,Set.mem_toFinset.mpr hCvw.mem_support_right⟩
    · obtain ⟨C,hC,hCvw⟩:=(localOrdinaryFactorGraph_adj D₀ v w).mp hadj
      have hv:v∈A:=by rw [←hD₀.2];exact Finset.mem_biUnion.mpr ⟨C,hC,Set.mem_toFinset.mpr hCvw.mem_support_left⟩
      have hw:w∈A:=by rw [←hD₀.2];exact Finset.mem_biUnion.mpr ⟨C,hC,Set.mem_toFinset.mpr hCvw.mem_support_right⟩
      exact ⟨Finset.mem_union_left _ hv,Finset.mem_union_left _ hw⟩
  have hno:∀ v w,v∈Z→w∈Z→¬(localOrdinaryFactorGraph D₁⊔localOrdinaryFactorGraph D₀).Adj v w:=by
    intro v w hv hw hadj
    simp only [SimpleGraph.sup_adj] at hadj
    rcases hadj with hadj|hadj
    · obtain ⟨C,hC,hCvw⟩:=(localOrdinaryFactorGraph_adj D₁ v w).mp hadj
      change C∈M₁.image f at hC
      obtain ⟨C₀,hC₀,rfl⟩:=Finset.mem_image.mp hC
      change C₀.val.val.Adj v w at hCvw
      have hvC:v∈ordinaryCycleVertices G r C₀:=by
        exact Set.mem_toFinset.mpr hCvw.mem_support_left
      have hwC:w∈ordinaryCycleVertices G r C₀:=by
        exact Set.mem_toFinset.mpr hCvw.mem_support_right
      have hvw:v=w:=Finset.card_le_one.mp (hroot C₀ hC₀) v
        (Finset.mem_inter.mpr ⟨hvC,hv⟩) w (Finset.mem_inter.mpr ⟨hwC,hw⟩)
      exact hCvw.ne hvw
    · obtain ⟨C,hC,hCvw⟩:=(localOrdinaryFactorGraph_adj D₀ v w).mp hadj
      have hvA:v∈A:=by
        rw [←hD₀.2]
        exact Finset.mem_biUnion.mpr ⟨C,hC,Set.mem_toFinset.mpr hCvw.mem_support_left⟩
      exact Finset.disjoint_left.mp hAZ hvA hv
  obtain ⟨hplus,hminus,hsub,hSp,hSm,hid⟩:=
    ordinary_hub_factor_trade (Q:=G) (F:=⊥) (T:=Finset.univ) (r:=r) A Z hAZ u u' hu D₀ D₁ hD₀ hD₁ hdis hH
  have hpHost:HasResourceDecomposition (ordinaryWheelResources (P:=G) (F:=⊥) (Hbase:=H) (r:=r))
      (ordinaryHostResources (localOrdinaryFactorGraph D₁⊔localOrdinaryFactorGraph D₀)
        (fun v z=>(v∈A∪Z∧z=u)∨(v∈A∧z=u'))):=by
    obtain ⟨M,hM,hcov⟩:=hplus
    exact ordinary_decomposition_recover_host G ⊥ H _ (ordinary_host_resources_monotone _ _ _ _ hsub hSp)
      M ⟨hM,hcov⟩ (by intro C _ v _ w _;simp)
  have hmHost:HasResourceDecomposition (ordinaryWheelResources (P:=G) (F:=⊥) (Hbase:=H) (r:=r))
      (ordinaryHostResources (localOrdinaryFactorGraph D₁⊔localOrdinaryFactorGraph D₀)
        (fun v z=>(v∈A∪Z∧z=u')∨(v∈A∧z=u))):=by
    obtain ⟨M,hM,hcov⟩:=hminus
    exact ordinary_decomposition_recover_host G ⊥ H _ (ordinary_host_resources_monotone _ _ _ _ hsub hSm)
      M ⟨hM,hcov⟩ (by intro C _ v _ w _;simp)
  exact ⟨_,hplus,hminus,hpHost,hmHost,hsub,hsupp,hno,hSp,hSm,hid⟩
end Oberwolfach
