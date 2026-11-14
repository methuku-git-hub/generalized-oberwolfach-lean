module

public import Oberwolfach.FactorSequentialRemoval
public import Oberwolfach.FactorRemovalMargin

@[expose] public section
/-! The small-class removal induction with the manuscript's original degree
margin. The single-copy embedding remains an explicit, separate obligation. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_small_class_removal {n:ℕ} (D:ℕ) (δ α:ℝ) (hδ:0≤δ) (hα:0<α)
    (G:SimpleGraph (Fin n)) (hG:G.IsRegularOfDegree D)
    (hdegree:(δ+α)*(n:ℝ)≤D)
    (F:List (SimpleGraph (Fin n))) (hsmall:(F.length:ℝ)≤α*n/500)
    (hcopy:∀ P:SimpleGraph (Fin n),∀ d:ℕ,P.IsRegularOfDegree d→
      (δ+α/2)*(n:ℝ)≤d→∀ A∈F,
      ∃ H:SimpleGraph (Fin n),H≤P ∧ H.IsRegularOfDegree 2 ∧ Nonempty (H ≃g A)):
    ∃ R:SimpleGraph (Fin n),∃ pieces:List (SimpleGraph (Fin n)),
      R.IsRegularOfDegree (D-2*F.length) ∧ R≤G ∧
      (δ+α/2)*(n:ℝ)≤((D-2*F.length:ℕ):ℝ) ∧
      List.Forall₂ (fun H A=>Nonempty (H ≃g A) ∧ H.IsRegularOfDegree 2) pieces F ∧
      (∀ H∈pieces,H≤G ∧ ∀ u v,H.Adj u v→¬R.Adj u v) ∧
      pieces.Pairwise (fun H J=>∀ u v,H.Adj u v→¬J.Adj u v) ∧
      (∀ u v,G.Adj u v ↔ R.Adj u v ∨ ∃ H∈pieces,H.Adj u v):=by
  let T:=⌈(δ+α/2)*(n:ℝ)⌉₊
  have hm:T+2*F.length≤D:=factor_small_removal_integer_margin D F.length n δ α hδ hα hdegree hsmall
  have hc:∀ P:SimpleGraph (Fin n),∀ d:ℕ,P.IsRegularOfDegree d→T≤d→
      ∀ A∈F,∃ H:SimpleGraph (Fin n),H≤P ∧ H.IsRegularOfDegree 2 ∧ Nonempty (H ≃g A):=by
    intro P d hp hd A hA
    apply hcopy P d hp _ A hA
    have hceil:(δ+α/2)*(n:ℝ)≤(T:ℝ):=Nat.le_ceil _
    exact hceil.trans (by exact_mod_cast hd)
  obtain ⟨R,pieces,hR,hRG,hrel,hpairR,hpair,hexact⟩:=factor_sequential_removal T D G hG F hm hc
  have hmargin: (δ+α/2)*(n:ℝ)≤((D-2*F.length:ℕ):ℝ):=
    (factor_small_removal_margin D F.length n δ α hδ hα hdegree hsmall F.length (le_refl _)).2
  exact ⟨R,pieces,hR,hRG,hmargin,hrel,hpairR,hpair,hexact⟩
end Oberwolfach
