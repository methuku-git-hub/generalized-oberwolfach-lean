module

public import Oberwolfach.PrescribedEmbeddingActualSaturation
public import Oberwolfach.PrescribedEmbeddingTotalSize

@[expose] public section
/-! Every free occurrence is a vertex of one of the source factors, so the
source-size bound controls the actual saturated host vertices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem prescribed_embedding_saturation_from_source_family
    {I V:Type} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
    {X:I→Type} (Q:∀ i,Finset (X i)) (T:Finset (Σ i,X i)) (φ:(Σ i,X i)→V)
    (δ n:ℝ) (hδ:0<δ) (hn:0<n) (hI:(Fintype.card I:ℝ)≤n)
    (hQ:∀ i,((Q i).card:ℝ)≤δ*n) (hT:T⊆Finset.univ.sigma Q):
    ((Finset.univ.filter (fun v=>Real.sqrt δ*n≤((T.filter (fun x=>φ x=v)).card:ℝ))).card:ℝ)≤Real.sqrt δ*n := by
  have hcard:T.card≤∑ i,(Q i).card:=by
    calc
      T.card≤(Finset.univ.sigma Q).card:=Finset.card_le_card hT
      _ = _ :=by simp [Finset.card_sigma]
  have htotal:=prescribed_embedding_total_size (fun i=>(Q i).card) δ n hδ.le hn.le hI hQ
  have hTR:(T.card:ℝ)≤δ*n^2:=by
    have hh:((T.card:ℝ)≤((∑ i,(Q i).card:ℕ):ℝ)):=by exact_mod_cast hcard
    linarith
  exact prescribed_embedding_saturated_actual_occurrences T φ δ n hδ hn hTR
end Oberwolfach
