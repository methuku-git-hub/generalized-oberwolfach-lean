module

public import Oberwolfach.PrescribedFamilyState
public import Oberwolfach.PrescribedProductFamilySaturation
public import Oberwolfach.PrescribedActualForbiddenBudget
public import Oberwolfach.PrescribedAllComponentBudgets

@[expose] public section
/-! Construct the forbidden graph and the saturation bound from the current
family state and the original quantitative hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I X V:Type} [Fintype I] [Fintype X] [Fintype V] [DecidableEq I] [DecidableEq X] [DecidableEq V]

theorem prescribed_family_state_resources
    (st:PrescribedFamilyState I X V) (QV:I→Finset X) (Q:I→SimpleGraph X)
    (A₀:I→Finset X) (ψ:I→X→V) (E₀:I→Finset (Sym2 V)) (J:SimpleGraph V)
    (β δ n:ℝ) (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/100)^2)
    (hnβ:100/β≤n) (hn:2/Real.sqrt δ≤n)
    (hI:(Fintype.card I:ℝ)≤n) (hQsize:∀ i,((QV i).card:ℝ)≤δ*n)
    (hQdegree:∀ i x,(Q i).degree x≤2)
    (hold:∀ v,((Finset.univ.filter (fun i=>∃ x,x∈A₀ i ∧ ψ i x=v)).card:ℝ)≤δ*n)
    (hJ:∀ v,(J.degree v:ℝ)≤δ*n)
    (hvalid:st.Valid QV Q A₀ ψ E₀ J (Real.sqrt δ*n)):
    let S:=Finset.univ.filter (fun v=>(Real.sqrt δ*n:ℝ)≤
      (st.freeOccurrences.filter (fun p=>familyVertexImage st.vertexMap p=v)).card);
    (S.card:ℝ)≤Real.sqrt δ*n ∧
    ∃ F:SimpleGraph V,(∀ v,(F.degree v:ℝ)≤8*Real.sqrt δ*n) ∧
      J.edgeFinset⊆F.edgeFinset ∧ (∀ i,st.physicalEdges i⊆F.edgeFinset) ∧
      ∀ (k:I) (as:List X),as.Nodup→st.assigned k∪as.toFinset⊆QV k→
        Disjoint (st.assigned k) as.toFinset→
        let b:ℝ:=((st.assigned k).image (st.vertexMap k) ∪ S).card;
        b+as.length+2+8*Real.sqrt δ*n<β*n ∧
        b+as.length+1+8*Real.sqrt δ*n<β*n ∧
        b+as.length+2+2*(8*Real.sqrt δ*n)<β*n ∧
        b+(as.length+1:ℕ)+2+2*(8*Real.sqrt δ*n)<β*n := by
  intro S
  have hroot:0<Real.sqrt δ:=Real.sqrt_pos.2 hδ
  have hnpos:0<n:=by have :0<2/Real.sqrt δ:=div_pos (by norm_num) hroot;linarith
  have hT:∀ p∈st.freeOccurrences,p.2∈QV p.1:=by
    intro p hp
    apply hvalid.2.2.1 p.1
    exact (hvalid.2.1 p.1 p.2).mpr (Or.inr hp)
  have hS:(S.card:ℝ)≤Real.sqrt δ*n:=by
    exact prescribed_product_family_saturation QV st.freeOccurrences (familyVertexImage st.vertexMap)
      δ n hδ hnpos hI hQsize hT
  have hfree:∀ v,((st.freeOccurrences.filter (fun p=>st.vertexMap p.1 p.2=v)).card:ℝ)≤Real.sqrt δ*n+1:=by
    intro v
    have heq:st.freeOccurrences.filter (fun p=>familyVertexImage st.vertexMap p=v) =
        st.freeOccurrences.filter (fun p=>st.vertexMap p.1 p.2=v):=by
      ext p
      simp only [familyVertexImage, Finset.mem_filter]
      exact Finset.mem_filter
    rw [←heq]
    exact hvalid.2.2.2.2.1 v
  obtain ⟨F,hF,hJF,hEF⟩:=prescribed_actual_forbidden_budget Q st.assigned A₀ st.vertexMap ψ st.freeOccurrences
    hvalid.1 hvalid.2.1 hvalid.2.2.2.1 hQdegree st.sourceEdges st.physicalEdges
    hvalid.2.2.2.2.2.2.2.1 hvalid.2.2.2.2.2.1 hvalid.2.2.2.2.2.2.1
    β δ n hβ hβ1 hδ hδbound hn hold hfree J hJ
  refine ⟨hS,F,hF,hJF,hEF,?_⟩
  intro k as has hsub hdis
  have hM:0≤8*Real.sqrt δ*n:=by positivity
  exact prescribed_all_component_budgets (QV k) (st.assigned k) as has hsub hdis
    (st.vertexMap k) S (8*Real.sqrt δ*n) β δ n hβ hβ1 hδ hδbound hnβ (hQsize k) hS hM le_rfl
end Oberwolfach
