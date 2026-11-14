module

public import Oberwolfach.OrdinaryGeneralFinishResult
public import Oberwolfach.OrdinaryCleanupPostFacts
public import Oberwolfach.OrdinarySequentialWheelDecompositions
public import Oberwolfach.LongThreeGraphDegree

@[expose] public section
/-! Combine the approximate packing, cleanup and boundary finish into one
wheel decomposition of the edges removed from the original host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_combine_packing_cleanup_finish
    (m:ℕ) (Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (R:SimpleGraph (V⊕U)) (t ν ρ:ℝ) (Kcap Dmax:ℕ)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,(m+1)∣(Finset.univ.filter (fun v=>H v u)).card)
    (M:OrdinaryUnreservedPackingData Q F H X Z R (m+1) t):
    let C:=ordinaryPackingUsedGraph Q F H X Z R (m+1) t M;
    let Q₁:=ordinaryPackingPostRim Q F H X Z R (m+1) t M;
    let H₁:=ordinaryPackingPostSpokes Q F H X Z R (m+1) t M;
    ∀(K:OrdinaryOutsideCleanupData Q₁ F H₁ X Z C (m+1) ν),
    let Q₂:=ordinaryCleanupPostRim Q₁ F H₁ X Z C (m+1) ν K;
    let H₂:=ordinaryCleanupPostSpokes Q₁ F H₁ X Z C (m+1) ν K;
    OrdinaryGeneralFinishResult Q₂ H₂ X Z m Kcap Dmax ρ→
    ∃Rtotal:SimpleGraph V,∃Stotal:V→U→Prop,
      Rtotal≤Q ∧ (∀v u,Stotal v u→H v u) ∧ HasOrdinaryWheelDecomposition Rtotal Stotal (m+1) ∧
      let Qnext:=Q\Rtotal;let Hnext:=fun v u=>H v u∧¬Stotal v u;
      Qnext≤spanningRestriction Q₂ X ∧ (∀v u,Hnext v u→H₂ v u∧v∈X∧u∈Z) ∧
      (∀v,Qnext.degree v=2*(Finset.univ.filter (Hnext v)).card) ∧
      (∀u,(m+1)∣(Finset.univ.filter (fun v=>Hnext v u)).card) ∧
      ordinaryHostResources Qnext Hnext⊆ordinaryRootResources X Z ∧
      (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph Rtotal Stotal) (ordinaryInnerVertices X Z)).degree w:ℝ)≤
        ν+2*(ρ*Fintype.card (V⊕U))+((3*(Kcap+Dmax)+Dmax*(m+1):ℕ):ℝ)):=by
  intro C Q₁ H₁ K Q₂ H₂ hfinish
  let R₁:=ordinaryWheelRimGraph M.wheels
  let S₁:=ordinaryPackingSpokes M.wheels
  let R₂:=wheelFamilyRim K.wheels
  let S₂:=wheelFamilySpokes K.wheels
  have hm:=ordinary_packing_post_facts Q F H X Z R (m+1) t M hbal hdiv
  have hsub₁:R₁≤Q:=(ordinaryWheelRimGraph_subhost M.wheels).trans (by
    intro v w h;exact h.1.1)
  have hS₁:∀v u,S₁ v u→H v u:=by
    intro v u h
    obtain ⟨W,hW,hu,hv⟩:=h
    have hh:ordinaryUnreservedSpokes H X Z R v u:=by
      rw [←hu]
      exact W.property.1 v hv
    exact hh.1
  have hCsub:C≤ordinaryPhysicalGraph Q H:=by
    intro a b hab
    cases a with
    | inl v=>cases b with
      | inl w=>exact hsub₁ hab
      | inr u=>exact hS₁ v u hab
    | inr u=>cases b with
      | inl v=>exact hS₁ v u hab
      | inr u'=>exact hab.elim
  have hsub₂:=wheelFamily_subhost K.wheels
  have hdec₁:HasOrdinaryWheelDecomposition R₁ S₁ (m+1):=ordinaryPacking_decomposition M.wheels M.disjoint
  obtain ⟨R₃,S₃,hR₃,hS₃,hdec₃,hrest⟩:=hfinish
  obtain ⟨hnext,hnextS,hnextBal,hnextDiv,hroot,hdegree⟩:=hrest
  have hseq:=ordinary_sequential_wheel_decompositions Q R₁ R₂ R₃ H S₁ S₂ S₃ (m+1)
    hsub₂.1 hR₃ hsub₂.2 hS₃ hdec₁ K.decomposition hdec₃
  refine ⟨(R₁⊔R₂)⊔R₃,fun v u=>(S₁ v u∨S₂ v u)∨S₃ v u,?_,?_,hseq.1,?_⟩
  · intro v w hvw
    rcases hvw with (h₁|h₂)|h₃
    · exact hsub₁ h₁
    · exact (hsub₂.1 h₂).1
    · exact ((hR₃ h₃).1).1
  · intro v u hvu
    rcases hvu with (h₁|h₂)|h₃
    · exact hS₁ v u h₁
    · exact (hsub₂.2 v u h₂).1
    · exact ((hS₃ v u h₃).1).1
  · let Inv (Qn:SimpleGraph V) (Hn:V→U→Prop):Prop:=
      Qn≤spanningRestriction Q₂ X ∧ (∀v u,Hn v u→H₂ v u∧v∈X∧u∈Z) ∧
      (∀v,Qn.degree v=2*(Finset.univ.filter (Hn v)).card) ∧
      (∀u,(m+1)∣(Finset.univ.filter (fun v=>Hn v u)).card) ∧
      ordinaryHostResources Qn Hn⊆ordinaryRootResources X Z
    have hInv:Inv (Q₂\R₃) (fun v u=>H₂ v u∧¬S₃ v u):=by
      refine ⟨hnext,hnextS,?_,?_,hroot⟩
      · convert hnextBal using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
      · convert hnextDiv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    have hInv':Inv (Q\((R₁⊔R₂)⊔R₃)) (fun v u=>H v u∧¬((S₁ v u∨S₂ v u)∨S₃ v u)):=by
      rw [hseq.2.1,hseq.2.2]
      exact hInv
    refine ⟨hInv'.1,hInv'.2.1,?_,?_,hInv'.2.2.2.2,?_⟩
    · convert hInv'.2.2.1 using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    · convert hInv'.2.2.2.1 using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    · intro w
      let I:=ordinaryInnerVertices X Z
      let D:=ordinaryCleanupUsedGraph Q₁ F H₁ X Z C (m+1) ν K
      have hgraph:ordinaryPhysicalGraph ((R₁⊔R₂)⊔R₃) (fun v u=>(S₁ v u∨S₂ v u)∨S₃ v u)=
          (C⊔D)⊔ordinaryPhysicalGraph R₃ S₃:=by
        ext a b
        cases a <;> cases b <;> simp [ordinaryPhysicalGraph,C,D,R₁,R₂,S₁,S₂,ordinaryPackingUsedGraph,ordinaryCleanupUsedGraph]
      have hsub:spanningRestriction (ordinaryPhysicalGraph ((R₁⊔R₂)⊔R₃)
          (fun v u=>(S₁ v u∨S₂ v u)∨S₃ v u)) I≤D⊔spanningRestriction (ordinaryPhysicalGraph R₃ S₃) I:=by
        intro a b hab
        have hi:=(spanningRestriction_adj _ _ _ _).mp hab
        rw [hgraph] at hi
        rcases hi.1 with (hc|hd)|hf
        · have hcI:(spanningRestriction (ordinaryPhysicalGraph Q H) I).Adj a b:=by
            exact (spanningRestriction_adj _ _ _ _).mpr ⟨hCsub hc,hi.2.1,hi.2.2⟩
          exact ((disjoint_iff_inf_le.mp hm.inner_avoided) ⟨hc,hcI⟩).elim
        · exact Or.inl hd
        · exact Or.inr ((spanningRestriction_adj _ _ _ _).mpr ⟨hf,hi.2.1,hi.2.2⟩)
      have hd₁:=SimpleGraph.degree_le_of_le hsub (v:=w)
      have hd₂:=graph_degree_sup_le D (spanningRestriction (ordinaryPhysicalGraph R₃ S₃) I) w
      have hd₁r:((spanningRestriction (ordinaryPhysicalGraph ((R₁⊔R₂)⊔R₃)
          (fun v u=>(S₁ v u∨S₂ v u)∨S₃ v u)) I).degree w:ℝ)≤
          (D.degree w:ℝ)+((spanningRestriction (ordinaryPhysicalGraph R₃ S₃) I).degree w:ℝ):=by
        have hh:=hd₁.trans hd₂
        exact_mod_cast hh
      have hD:(D.degree w:ℝ)≤ν:=K.degree w
      linarith only [hd₁r,hD,hdegree w]
end Oberwolfach
