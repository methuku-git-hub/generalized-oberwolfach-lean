module

public import Oberwolfach.PrescribedActualForbiddenGraph
public import Oberwolfach.PrescribedSourceEdgesImage
public import Oberwolfach.PrescribedEmbeddingNumerics

@[expose] public section
/-! From the original prescribed/free occurrence bounds and tracked source
edges, construct the actual forbidden graph with the manuscript's 8t bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {I X V:Type} [Fintype I] [Fintype X] [Fintype V]
  [DecidableEq I] [DecidableEq X] [DecidableEq V]

theorem prescribed_actual_forbidden_budget
    (Q:I→SimpleGraph X) (A A₀:I→Finset X) (f ψ:I→X→V) (T:Finset (I×X))
    (hinj:FamilyPartialInjections A f)
    (hdom:∀ i x,x∈A i ↔ x∈A₀ i ∨ (i,x)∈T)
    (hpres:∀ i x,x∈A₀ i→f i x=ψ i x) (hQ:∀ i x,(Q i).degree x≤2)
    (R:I→Finset (Sym2 X)) (E:I→Finset (Sym2 V))
    (hrepr:∀ i,E i=(R i).image (Sym2.map (f i)))
    (hsource:∀ i,R i⊆(Q i).edgeFinset)
    (hends:∀ i e,e∈R i→∀ x∈e.toFinset,x∈A i)
    (β δ n:ℝ) (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/100)^2)
    (hn:2/Real.sqrt δ≤n)
    (hold:∀ v,((Finset.univ.filter (fun i=>∃ x,x∈A₀ i ∧ ψ i x=v)).card:ℝ)≤δ*n)
    (hfree:∀ v,((T.filter (fun p=>f p.1 p.2=v)).card:ℝ)≤Real.sqrt δ*n+1)
    (J:SimpleGraph V) (hJ:∀ v,(J.degree v:ℝ)≤δ*n):
    ∃ F:SimpleGraph V,(∀ v,(F.degree v:ℝ)≤8*Real.sqrt δ*n) ∧
      J.edgeFinset⊆F.edgeFinset ∧ (∀ i,E i⊆F.edgeFinset) := by
  obtain ⟨F,hF,hJF,hHi⟩:=prescribed_actual_forbidden_graph Q A A₀ f ψ T hinj hdom hpres hQ δ n (Real.sqrt δ*n) hold hfree J hJ
  have hnum:=prescribed_embedding_margins_from_hypotheses β δ n hβ hβ1 hδ hδbound hn
  refine ⟨F,?_,hJF,?_⟩
  · intro v
    have hv:=hF v
    nlinarith [hnum.2.1]
  · intro i
    rw [hrepr i]
    exact (prescribed_source_edges_image_contained (Q i) (A i) (f i) (hinj i) (R i) (hsource i) (hends i)).trans (hHi i)
end Oberwolfach
