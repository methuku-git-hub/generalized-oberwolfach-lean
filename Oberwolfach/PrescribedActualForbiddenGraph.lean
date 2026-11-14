module

public import Oberwolfach.PrescribedForbiddenGraph
public import Oberwolfach.PrescribedFamilyOccurrenceProjection
public import Oberwolfach.PrescribedPartialEmbedding
public import Oberwolfach.PrescribedInducedDegree

@[expose] public section
/-! Construct the forbidden graph from the assigned subgraphs of the actual
source factors and the actual prescribed/free occurrence bounds. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {I X V:Type} [Fintype I] [Fintype X] [Fintype V]
  [DecidableEq I] [DecidableEq X] [DecidableEq V]

theorem prescribed_actual_forbidden_graph
    (Q:I→SimpleGraph X) (A A₀:I→Finset X) (f ψ:I→X→V) (T:Finset (I×X))
    (hinj:FamilyPartialInjections A f)
    (hdom:∀ i x,x∈A i ↔ x∈A₀ i ∨ (i,x)∈T)
    (hpres:∀ i x,x∈A₀ i→f i x=ψ i x)
    (hQ:∀ i x,(Q i).degree x≤2)
    (δ n t:ℝ)
    (hold:∀ v,((Finset.univ.filter (fun i=>∃ x,x∈A₀ i ∧ ψ i x=v)).card:ℝ)≤δ*n)
    (hfree:∀ v,((T.filter (fun p=>f p.1 p.2=v)).card:ℝ)≤t+1)
    (J:SimpleGraph V) (hJ:∀ v,(J.degree v:ℝ)≤δ*n):
    ∃ F:SimpleGraph V,(∀ v,(F.degree v:ℝ)≤3*δ*n+2*t+2) ∧
      J.edgeFinset⊆F.edgeFinset ∧
      ∀ i,((Q i).induce (↑(A i):Set X) |>.map (prescribedPartialEmbedding (A i) (f i) (hinj i))).edgeFinset⊆F.edgeFinset := by
  let X' : I→Type:=fun i=>{x // x∈A i}
  let Q' : ∀ i,SimpleGraph (X' i):=fun i=>(Q i).induce (↑(A i):Set X)
  let φ : ∀ i,X' i↪V:=fun i=>prescribedPartialEmbedding (A i) (f i) (hinj i)
  let H:I→SimpleGraph V:=fun i=>(Q' i).map (φ i)
  let old:I→V→Prop:=fun i v=>∃ x,x∈A₀ i ∧ ψ i x=v
  let fresh:I→V→Prop:=fun i v=>∃ x,(i,x)∈T ∧ f i x=v
  have hsource:∀ i,H i≤(Q' i).map (φ i):=fun _=>le_rfl
  have hdegree:∀ i x,(Q' i).degree x≤2:=by
    intro i x
    exact (prescribed_induced_degree_le (Q i) (A i) x).trans (hQ i x.1)
  have hocc:∀ i v,(∃ x,φ i x=v)→ old i v ∨ fresh i v:=by
    intro i v hex
    obtain ⟨x,hx⟩:=hex
    have hA: x.1∈A₀ i ∨ (i,x.1)∈T:=(hdom i x.1).mp x.2
    rcases hA with hA|hA
    · left
      refine ⟨x.1,hA,?_⟩
      exact (hpres i x.1 hA).symm.trans hx
    · exact Or.inr ⟨x.1,hA,hx⟩
  have hold':∀ v,((Finset.univ.filter (fun i=>old i v)).card:ℝ)≤δ*n:=by
    intro v
    have hsub:(Finset.univ.filter (fun i=>old i v))⊆
        (Finset.univ.filter (fun i=>∃ x,x∈A₀ i ∧ ψ i x=v)):=by
      intro i hi
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
      exact hi
    have hc:((Finset.univ.filter (fun i=>old i v)).card:ℝ)≤
        ((Finset.univ.filter (fun i=>∃ x,x∈A₀ i ∧ ψ i x=v)).card:ℝ):=by exact_mod_cast Finset.card_le_card hsub
    exact hc.trans (hold v)
  have hfresh':∀ v,((Finset.univ.filter (fun i=>fresh i v)).card:ℝ)≤t+1:=by
    intro v
    have hsub:(Finset.univ.filter (fun i=>fresh i v))⊆
        (Finset.univ.filter (fun i=>∃ x,(i,x)∈T ∧ f i x=v)):=by
      intro i hi
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
      exact hi
    have hc:((Finset.univ.filter (fun i=>fresh i v)).card:ℝ)≤
        ((Finset.univ.filter (fun i=>∃ x,(i,x)∈T ∧ f i x=v)).card:ℝ):=by exact_mod_cast Finset.card_le_card hsub
    have hsub':(Finset.univ.filter (fun i=>∃ x,(i,x)∈T ∧ f i x=v))⊆
        (T.filter (fun p=>f p.1 p.2=v)).image Prod.fst:=by
      intro i hi
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi
      obtain ⟨x,hx,hxv⟩:=hi
      exact Finset.mem_image.mpr ⟨(i,x),Finset.mem_filter.mpr ⟨hx,hxv⟩,rfl⟩
    have hnat':(Finset.univ.filter (fun i=>∃ x,(i,x)∈T ∧ f i x=v)).card≤
        (T.filter (fun p=>f p.1 p.2=v)).card:=
      (Finset.card_le_card hsub').trans Finset.card_image_le
    have hreal:((Finset.univ.filter (fun i=>∃ x,(i,x)∈T ∧ f i x=v)).card:ℝ)≤
        ((T.filter (fun p=>f p.1 p.2=v)).card:ℝ):=by exact_mod_cast hnat'
    exact hc.trans (hreal.trans (hfree v))
  let G:SimpleGraph V:=⨆ i,H i
  let F:SimpleGraph V:=G⊔J
  have hh:=prescribed_forbidden_graph_from_partial_images X' Q' φ H old fresh hsource hdegree hocc J δ n t (by
    intro v
    convert hold' v using 1
    congr 1
    congr 1
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]) (by
    intro v
    convert hfresh' v using 1
    congr 1
    congr 1
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]) hJ
  refine ⟨F,?_,?_,?_⟩
  · intro v
    exact (hh.1 v).2
  · intro e he
    simp only [SimpleGraph.mem_edgeFinset] at he ⊢
    have hJF:J≤F:=by dsimp [F];exact le_sup_right
    exact SimpleGraph.edgeSet_mono hJF he
  · intro i e he
    simp only [SimpleGraph.mem_edgeFinset] at he ⊢
    change e∈(H i).edgeSet at he
    have hHi:H i≤F:=by
      dsimp [F,G]
      exact (le_iSup H i).trans le_sup_left
    exact SimpleGraph.edgeSet_mono hHi he
end Oberwolfach
