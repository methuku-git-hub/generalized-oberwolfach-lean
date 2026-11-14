module

public import Oberwolfach.PrescribedEmbeddingActualSaturation
public import Oberwolfach.PrescribedEmbeddingTotalSize

@[expose] public section
/-! Bound saturated labels from actual free occurrences in a family whose
source vertex sets may vary with the factor. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {I X V:Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq X] [DecidableEq V]

theorem prescribed_product_family_saturation (QV:I→Finset X) (T:Finset (I×X))
    (φ:I×X→V) (δ n:ℝ) (hδ:0<δ) (hn:0<n) (hI:(Fintype.card I:ℝ)≤n)
    (hQ:∀ i,((QV i).card:ℝ)≤δ*n) (hT:∀ p∈T,p.2∈QV p.1):
    ((Finset.univ.filter (fun v=>Real.sqrt δ*n≤((T.filter (fun p=>φ p=v)).card:ℝ))).card:ℝ)≤Real.sqrt δ*n := by
  let U:Finset (I×X):=Finset.univ.biUnion (fun i=>({i}:Finset I).product (QV i))
  have hsub:T⊆U:=by
    intro p hp
    apply Finset.mem_biUnion.mpr
    refine ⟨p.1,Finset.mem_univ _,?_⟩
    exact Finset.mem_product.mpr ⟨by simp,hT p hp⟩
  have hcard:T.card≤∑ i,(QV i).card:=by
    calc
      T.card≤U.card:=Finset.card_le_card hsub
      _≤∑ i,(({i}:Finset I).product (QV i)).card:=Finset.card_biUnion_le
      _=∑ i,(QV i).card:=by simp [Finset.card_product]
  have htotal:=prescribed_embedding_total_size (fun i=>(QV i).card) δ n hδ.le hn.le hI hQ
  have hTR:(T.card:ℝ)≤δ*n^2:=by
    have hh:((T.card:ℝ)≤((∑ i,(QV i).card:ℕ):ℝ)):=by exact_mod_cast hcard
    linarith
  exact prescribed_embedding_saturated_actual_occurrences T φ δ n hδ hn hTR
end Oberwolfach
