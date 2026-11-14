module

public import Oberwolfach.MarkedSeedFailureMargin
public import Oberwolfach.OrdinarySeedFailureMargin

@[expose] public section
/-! A single threshold controls the sum of the marked and finitely many
ordinary seed concentration failure probabilities. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem eventually_mixed_seed_failure_below
    (d m K:ℕ) (ℓ:Fin K→ℕ) (BM:ℝ) (BO:Fin K→ℝ) (t δ:ℝ)
    (hBM:0<BM) (hBO:∀i,0<BO i) (ht:0<t) (hδ:0<δ):
    ∃N:ℕ,∀n:ℕ,N≤n→∀U:Type,[Fintype U]→Fintype.card U≤n→
    let errM:ℝ:=(Fintype.card ((((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))):ℝ)*
      (2*Real.exp (-2*t^2/((8*(d:ℝ)+6)^2*(((m:ℝ)+1)^4*BM/n)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*BM))))
    let errO:Fin K→ℝ:=fun i=>(Fintype.card ((Fin n×Fin n)⊕(Fin n×U)):ℝ)*
      (2*Real.exp (-2*t^2/((8*(d:ℝ)+6)^2*(((ℓ i:ℝ)+1)^3*BO i/n)*(2*((ℓ i:ℝ)+1))*(((ℓ i:ℝ)+1)^2*BO i))))
    errM+∑i,errO i<δ:=by
  let δ₀:=δ/((K:ℝ)+1)
  have hδ₀:0<δ₀:=by dsimp [δ₀];positivity
  obtain ⟨NM,hNM⟩:=eventually_marked_seed_failure_below d m BM t δ₀ hBM ht hδ₀
  have hO:∀i:Fin K,∃N:ℕ,∀n:ℕ,N≤n→∀U:Type,[Fintype U]→Fintype.card U≤n→
      (Fintype.card ((Fin n×Fin n)⊕(Fin n×U)):ℝ)*
        (2*Real.exp (-2*t^2/((8*(d:ℝ)+6)^2*(((ℓ i:ℝ)+1)^3*BO i/n)*(2*((ℓ i:ℝ)+1))*(((ℓ i:ℝ)+1)^2*BO i))))<δ₀ :=by
    intro i
    exact eventually_ordinary_seed_failure_below d (ℓ i) (BO i) t δ₀ (hBO i) ht hδ₀
  choose NO hNO using hO
  refine ⟨max NM (Finset.univ.sup NO),?_⟩
  intro n hn U _ hu errM errO
  have hnM:NM≤n:=le_trans (le_max_left _ _) hn
  have hnO:∀i,NO i≤n:=by
    intro i
    exact le_trans (Finset.le_sup (f:=NO) (Finset.mem_univ i)) (le_trans (le_max_right _ _) hn)
  have hm:errM<δ₀:=hNM n hnM U hu
  have ho:∀i,errO i≤δ₀:=fun i=>(hNO i n (hnO i) U hu).le
  have hsum:∑i,errO i≤(K:ℝ)*δ₀:=by
    calc
      _ ≤ ∑_i:Fin K,δ₀:=Finset.sum_le_sum (fun i _=>ho i)
      _ = (K:ℝ)*δ₀:=by simp
  have heq:δ₀+(K:ℝ)*δ₀=δ:=by
    dsimp [δ₀]
    field_simp
    ring
  linarith
end Oberwolfach
