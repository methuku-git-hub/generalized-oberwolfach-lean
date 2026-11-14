module

public import Oberwolfach.BoundedImageUnionDegrees

@[expose] public section
/-! Degree bound for used physical edges, separating prescribed and free
vertex occurrences. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {V I:Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem prescribed_embedding_used_degree_bound
    (H:I→SimpleGraph V) (old fresh:I→V→Prop)
    (hdeg:∀ i v,(H i).degree v≤(if old i v ∨ fresh i v then 2 else 0))
    (G J K:SimpleGraph V)
    (hcover:∀ v,G.neighborFinset v⊆Finset.univ.biUnion (fun i=>(H i).neighborFinset v))
    (hforbid:∀ v,K.neighborFinset v⊆G.neighborFinset v∪J.neighborFinset v)
    (δ n t:ℝ)
    (hold:∀ v,((Finset.univ.filter (fun i=>old i v)).card:ℝ)≤δ*n)
    (hfresh:∀ v,((Finset.univ.filter (fun i=>fresh i v)).card:ℝ)≤t+1)
    (hJ:∀ v,(J.degree v:ℝ)≤δ*n):
    ∀ v,(G.degree v:ℝ)≤2*δ*n+2*t+2 ∧ (K.degree v:ℝ)≤3*δ*n+2*t+2 := by
  intro v
  have hu:(Finset.univ.filter (fun i=>old i v ∨ fresh i v)).card≤
      (Finset.univ.filter (fun i=>old i v)).card+(Finset.univ.filter (fun i=>fresh i v)).card:=by
    rw [Finset.filter_or]
    exact Finset.card_union_le _ _
  have hGnat:G.degree v≤2*(Finset.univ.filter (fun i=>old i v ∨ fresh i v)).card:=by
    rw [←SimpleGraph.card_neighborFinset_eq_degree]
    have hh:=degree_two_image_union_bound H (fun i w=>old i w ∨ fresh i w) (by
      intro i w
      by_cases ho:old i w ∨ fresh i w <;> simpa [ho] using hdeg i w) v
    apply (Finset.card_le_card (hcover v)).trans
    apply hh.trans
    apply Nat.mul_le_mul_left
    apply Finset.card_le_card
    intro i hi
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hi
  have hGR:(G.degree v:ℝ)≤2*((Finset.univ.filter (fun i=>old i v ∨ fresh i v)).card:ℝ):=by exact_mod_cast hGnat
  have huR:((Finset.univ.filter (fun i=>old i v ∨ fresh i v)).card:ℝ)≤
      ((Finset.univ.filter (fun i=>old i v)).card:ℝ)+(Finset.univ.filter (fun i=>fresh i v)).card:=by exact_mod_cast hu
  have hKnat:K.degree v≤G.degree v+J.degree v:=by
    rw [←SimpleGraph.card_neighborFinset_eq_degree,←SimpleGraph.card_neighborFinset_eq_degree,←SimpleGraph.card_neighborFinset_eq_degree]
    exact (Finset.card_le_card (hforbid v)).trans (Finset.card_union_le _ _)
  have hKR:(K.degree v:ℝ)≤(G.degree v:ℝ)+(J.degree v:ℝ):=by exact_mod_cast hKnat
  have h1:=hold v
  have h2:=hfresh v
  have h3:=hJ v
  constructor <;> nlinarith
end Oberwolfach
