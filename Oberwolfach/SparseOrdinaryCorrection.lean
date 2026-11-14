module

public import Oberwolfach.SparseCorrectionMatrices
public import Oberwolfach.SparseCorrectionScales
public import Oberwolfach.CorrectionGraphRealization

@[expose] public section

/-! The manuscript's sparse ordinary degree-correction lemma. All integer
demands and graph deletions are constructed, and the order threshold is
chosen before the graph, orientation and forbidden sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
universe u v
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem sparse_ordinary_degree_correction
    (r : ℕ) (hr : 3≤r) (ω h δ ξ : ℝ)
    (hω : 0<ω) (hh : 0<h) (hδ : 0<δ) (hδsmall : δ<1/4)
    (hξ : 0<ξ) (hξh : ξ≤h/100) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∃ n₀ : ℕ,∀ η : ℝ,0≤η → η≤η₀ →
      ∀ (V : Type u) (U : Type v) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
      n₀≤Fintype.card V → ω*Fintype.card V≤Fintype.card U →
      Fintype.card U≤Fintype.card V →
      ∀ (Q FQ : SimpleGraph V) (H FH : V → U → Prop) (A : V → V → ℕ),
      (∀ x y,A x y+A y x=if (Q \ FQ).Adj x y then 1 else 0) →
      BipartiteLargeCut A δ h →
      BipartiteLargeCut (fun v u=>if H v u ∧ ¬FH v u then 1 else 0) δ h →
      (∀ v,|(Q.degree v : ℝ)-2*(Finset.univ.filter (H v)).card|≤η*Fintype.card V) →
      ∃ (JQ : SimpleGraph V) (JH : V → U → Prop),
        JQ≤Q \ FQ ∧ (∀ v u,JH v u → H v u ∧ ¬FH v u) ∧
        (∀ v,(Q \ JQ).degree v=2*(Finset.univ.filter (fun u=>H v u ∧ ¬JH v u)).card) ∧
        (∀ u,r∣(Finset.univ.filter (fun v=>H v u ∧ ¬JH v u)).card) ∧
        (∀ v,(JQ.degree v : ℝ)+(Finset.univ.filter (JH v)).card≤10*ξ*Fintype.card V) ∧
        (∀ u,((Finset.univ.filter (fun v=>JH v u)).card : ℝ)≤10*ξ*Fintype.card V) := by
  classical
  obtain ⟨n₀,hn₀,hscale⟩ := sparse_correction_order_threshold r hδ hω hξ
  refine ⟨δ*ω*ξ/1000,by positivity,n₀,?_⟩
  intro η hη hηsmall V U _ _ _ _ hn hωn hsn Q FQ H FH A hA hcutA hcutH hb
  let n := Fintype.card V
  have hn1 : 1≤n := hn₀.trans hn
  have hnpos : 0<n := by omega
  have hnR : (0 : ℝ)<n := by exact_mod_cast hnpos
  have hspos : 0<Fintype.card U := by
    have hpos : (0 : ℝ)<Fintype.card U := (mul_pos hω hnR).trans_le hωn
    exact_mod_cast hpos
  have hω1 : ω≤1 := by
    have hsR : (Fintype.card U : ℝ)≤n := by exact_mod_cast hsn
    nlinarith
  let base := Nat.floor (ξ*n)
  have hnscale : 100*((r : ℝ)+2)≤δ*ω*ξ*n := hscale n hn
  obtain ⟨hrδ,hunit,hpositive,hrelative,hcapacity,hQbound,hHbound⟩ :=
    sparse_correction_numeric (by omega : 0<r) hδ (by linarith : δ≤1) hω hω1
      hξ hξh hη hηsmall hnscale
  change (r : ℝ)≤δ*base at hrδ
  change 1≤δ*ω*base at hunit
  change η*n+2≤2*ω*base at hpositive
  change 3/2+η*n≤δ*(ω*base-η*n/2) at hrelative
  change (base : ℝ)+r+η*n/2≤h*n/2 at hcapacity
  change 2*((base : ℝ)+r+1)+η*n≤4*ξ*n at hQbound
  change (base : ℝ)+r+1≤2*ξ*n at hHbound
  let b (v : V) : ℤ := (Q.degree v : ℤ)-2*(Finset.univ.filter (H v)).card
  let d (u : U) := (Finset.univ.filter (fun v=>H v u)).card
  have hb' (v : V) : |(b v : ℝ)|≤η*n := by
    simpa only [b,Int.cast_sub,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast] using hb v
  have heven : Even (∑ v,b v) := ordinary_degree_imbalance_even Q H
  obtain ⟨J,K,hJ,hK,hbalance,hresidue,hJbound,hKrowbound,hKcolbound⟩ :=
    sparse_integer_correction_matrices A (fun v u=>if H v u ∧ ¬FH v u then 1 else 0)
      d b base r (by omega) hnpos hspos hsn hω hωn hδ.le hδsmall
      (by positivity : 0≤η*n) hrδ hunit hpositive hrelative hcapacity hb' heven hcutA hcutH
  obtain ⟨JQ,hJQ,hJQdeg⟩ := graph_of_suborientation (Q \ FQ) A J (fun x y=>by
    by_cases hx : (Q \ FQ).Adj x y
    · simpa only [hx,ite_true] using hA x y
    · simpa only [hx,ite_false] using hA x y) hJ
  obtain ⟨JH,hJH,hJHrow,hJHcol⟩ := relation_from_submatrix
    (fun v u=>H v u ∧ ¬FH v u) K (fun v u=>by
      by_cases hvu : H v u ∧ ¬FH v u
      · simpa only [hvu,ite_true] using hK v u
      · simpa only [hvu,ite_false] using hK v u)
  have hJQ' : JQ≤Q := hJQ.trans (by intro x y hx;exact hx.1)
  have hJH' : ∀ v u,JH v u → H v u := fun v u hv=>(hJH v u hv).1
  have hHrowle (v : V) : (Finset.univ.filter (JH v)).card≤(Finset.univ.filter (H v)).card := by
    apply Finset.card_le_card
    intro u hu
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hu ⊢
    exact hJH' v u hu
  refine ⟨JQ,JH,hJQ,hJH,?_,?_,?_,?_⟩
  · intro v
    have hhbal := hbalance v
    rw [← hJHrow v] at hhbal
    have hphys := hJQdeg v
    have hdq := SimpleGraph.degree_le_of_le hJQ' (v:=v)
    have hdh := hHrowle v
    rw [graph_degree_sdiff Q JQ hJQ',relation_deleted_row_degree H JH hJH']
    dsimp [b] at hhbal
    omega
  · intro u
    rw [relation_deleted_column_degree H JH hJH']
    apply Nat.ModEq.dvd'
    change (Finset.univ.filter (fun v=>JH v u)).card%r=(Finset.univ.filter (fun v=>H v u)).card%r
    rw [hJHcol]
    exact hresidue u
  · intro v
    have hj : (JQ.degree v : ℝ)≤4*ξ*n := by
      rw [hJQdeg]
      push_cast
      simpa only [Nat.cast_sum] using (hJbound v).trans hQbound
    have hk : ((Finset.univ.filter (JH v)).card : ℝ)≤2*ξ*n := by
      rw [hJHrow]
      exact (hKrowbound v).trans hHbound
    change _≤10*ξ*n
    nlinarith [mul_nonneg hξ.le hnR.le]
  · intro u
    have hk : ((Finset.univ.filter (fun v=>JH v u)).card : ℝ)≤2*ξ*n := by
      rw [hJHcol]
      exact (hKcolbound u).trans (by linarith)
    change _≤10*ξ*n
    nlinarith [mul_nonneg hξ.le hnR.le]

end Oberwolfach
