module

public import Oberwolfach.FactorSmallClassEvenRemoval
public import Oberwolfach.FactorDecompositionSingleCopy

@[expose] public section
/-! The manuscript's density-one reduction supplies the single copy needed
by the sequential small-class removal, once the corresponding preparation
decompositions have been proved. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_small_class_from_decompositions {n:ℕ} (hn:0<n) (D:ℕ) (δ α:ℝ)
    (hδ:0≤δ) (hα:0<α) (G:SimpleGraph (Fin n))
    (hG:G.IsRegularOfDegree D) (hEven:Even D) (hdegree:(δ+α)*(n:ℝ)≤D)
    (F:List (SimpleGraph (Fin n))) (hF:∀ A∈F,A.IsRegularOfDegree 2)
    (hsmall:(F.length:ℝ)≤α*n/500)
    (hdecomp:∀ P:SimpleGraph (Fin n),∀ d:ℕ,P.IsRegularOfDegree d→Even d→
      (δ+α/2)*(n:ℝ)≤d→∀ A∈F,HasFactorDecomposition P (fun _:Fin (d/2)=>A)):
    ∃ R:SimpleGraph (Fin n),∃ pieces:List (SimpleGraph (Fin n)),
      R.IsRegularOfDegree (D-2*F.length) ∧ R≤G ∧
      (δ+α/2)*(n:ℝ)≤((D-2*F.length:ℕ):ℝ) ∧
      List.Forall₂ (fun H A=>Nonempty (H ≃g A) ∧ H.IsRegularOfDegree 2) pieces F ∧
      (∀ H∈pieces,H≤G ∧ ∀ u v,H.Adj u v→¬R.Adj u v) ∧
      pieces.Pairwise (fun H J=>∀ u v,H.Adj u v→¬J.Adj u v) ∧
      (∀ u v,G.Adj u v ↔ R.Adj u v ∨ ∃ H∈pieces,H.Adj u v):=by
  apply factor_small_class_even_removal D δ α hδ hα G hG hEven hdegree F hsmall
  intro P d hp he hd A hA
  have hnR:(0:ℝ)<n:=by exact_mod_cast hn
  have hval:0<(δ+α/2)*(n:ℝ):=by positivity
  have hd0:(0:ℝ)<d:=hval.trans_le hd
  have hd0':0<d:=by exact_mod_cast hd0
  have hd2:2≤d:=by obtain ⟨k,hk⟩:=he;omega
  have hq:0<d/2:=by omega
  exact factor_decomposition_single_copy hq P A (hF A hA) (hdecomp P d hp he hd A hA)
end Oberwolfach
