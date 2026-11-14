module

public import Oberwolfach.MappedFactorGraph
public import Oberwolfach.GraphSelectionDegrees
public import Oberwolfach.OrdinaryWheelFamilies
public import Oberwolfach.OrdinaryFactorWheels

@[expose] public section

/-! Convert the already selected factors into hub wheels without choosing
new factors or changing their parent candidate families. Spokes are required
only on the exact covered sets, not on their larger parent domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U J:Type} [Fintype V] [Fintype U] [Fintype J]
  [DecidableEq V] [DecidableEq U] [DecidableEq J]

theorem selected_hub_factor_wheels (Q F:SimpleGraph V) (H:V→U→Prop) (r:ℕ)
    (T Y:J→Finset V) (u:J↪U)
    (D:∀ j,Finset (LocalOrdinaryCycle Q F (T j) r))
    (hD:∀ j,∀ C∈D j,∀ C'∈D j,C≠C'→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices C'))
    (hcover:∀ j,(D j).biUnion localOrdinaryVertices=Y j)
    (hH:∀ j,∀ v∈Y j,H v (u j))
    (hcross:∀ i j,i≠j→Disjoint (localOrdinaryFactorGraph (D i)) (localOrdinaryFactorGraph (D j))):
    ∃ W:(Σ j,D j)→OrdinaryWheel Q F H r,
      (∀ i,ordinaryWheelRim (W i)=i.2.val.val.val.val ∧ ordinaryWheelHub (W i)=u i.1) ∧
      wheelFamilyRim W=(⨆ j,localOrdinaryFactorGraph (D j)) ∧
      (∀ a z,wheelFamilySpokes W a z↔∃ j,u j=z ∧ a∈Y j) ∧
      (∀ i j,i≠j→Disjoint (ordinaryWheelResources (W i)) (ordinaryWheelResources (W j))) ∧
      HasOrdinaryWheelDecomposition (wheelFamilyRim W) (wheelFamilySpokes W) r:=by
  have hmem (j:J) (C:D j) (a:V) (ha:a∈C.val.val.val.val.support):a∈Y j:=by
    rw [←hcover j]
    exact Finset.mem_biUnion.mpr ⟨C.val,C.property,Set.mem_toFinset.mpr ha⟩
  let W:(Σ j,D j)→OrdinaryWheel Q F H r:=fun i=>
    ⟨(i.2.val.val,u i.1),⟨fun a ha=>hH i.1 a (hmem i.1 i.2 a ha),i.2.val.property.2⟩⟩
  have hrim (i:Σ j,D j):ordinaryWheelRim (W i)=i.2.val.val.val.val:=rfl
  have hhub (i:Σ j,D j):ordinaryWheelHub (W i)=u i.1:=rfl
  have hdis (i j:Σ k,D k) (hne:i≠j):
      Disjoint (ordinaryWheelResources (W i)) (ordinaryWheelResources (W j)):=by
    by_cases hij:i.1=j.1
    · rcases i with ⟨k,C⟩;rcases j with ⟨l,C'⟩
      dsimp only at hij;subst l
      have hc:C.val≠C'.val:=by
        intro he;exact hne (congrArg (Sigma.mk k) (Subtype.ext he))
      have hcc:=hD k C.val C.property C'.val C'.property hc
      apply Finset.disjoint_left.mpr
      intro e he hf
      cases e with
      | inl e=>
        rw [ordinaryWheelResources_rim] at he hf
        induction e using Sym2.ind with
        | _ a b=>
          exact Finset.disjoint_left.mp hcc (Set.mem_toFinset.mpr he.mem_support_left)
            (Set.mem_toFinset.mpr hf.mem_support_left)
      | inr az=>
        rw [ordinaryWheelResources_spoke] at he hf
        exact Finset.disjoint_left.mp hcc (Set.mem_toFinset.mpr he.2) (Set.mem_toFinset.mpr hf.2)
    · apply Finset.disjoint_left.mpr
      intro e he hf
      cases e with
      | inl e=>
        rw [ordinaryWheelResources_rim] at he hf
        induction e using Sym2.ind with
        | _ a b=>
          have hi:(localOrdinaryFactorGraph (D i.1)).Adj a b:=
            (localOrdinaryFactorGraph_adj _ a b).mpr ⟨i.2.val,i.2.property,he⟩
          have hj:(localOrdinaryFactorGraph (D j.1)).Adj a b:=
            (localOrdinaryFactorGraph_adj _ a b).mpr ⟨j.2.val,j.2.property,hf⟩
          exact disjoint_graphs_no_common_edge _ _ (hcross i.1 j.1 hij) a b hi hj
      | inr az=>
        rw [ordinaryWheelResources_spoke] at he hf
        exact hij (u.injective ((hhub i).symm.trans (he.1.trans (hf.1.symm.trans (hhub j)))))
  refine ⟨W,fun i=>⟨hrim i,hhub i⟩,?_,?_,hdis,wheelFamily_decomposition W hdis⟩
  · ext a b
    simp only [wheelFamilyRim,SimpleGraph.iSup_adj,localOrdinaryFactorGraph_adj]
    constructor
    · rintro ⟨i,hi⟩;exact ⟨i.1,i.2.val,i.2.property,hi⟩
    · rintro ⟨j,C,hC,h⟩;exact ⟨⟨j,⟨C,hC⟩⟩,h⟩
  · intro a z
    constructor
    · rintro ⟨i,hi,ha⟩
      exact ⟨i.1,(hhub i).symm.trans hi,hmem i.1 i.2 a ha⟩
    · rintro ⟨j,hj,ha⟩
      rw [←hcover j] at ha
      obtain ⟨C,hC,ha⟩:=Finset.mem_biUnion.mp ha
      exact ⟨⟨j,⟨C,hC⟩⟩,hj,Set.mem_toFinset.mp ha⟩

end Oberwolfach
