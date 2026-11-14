module

public import Oberwolfach.GraphSelectionDegrees

@[expose] public section

/-! Sequential selection of actual edge-disjoint subgraphs. The only
candidate hypothesis is availability after every permitted local deletion.
The small potential bound is discharged by the uniform numerical theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem bounded_degree_selection_finite
    {V : Type*} [Fintype V] [DecidableEq V]
    (N D t B : ℕ) (ht : 0 < t) (q s M : ℝ) (hq : 0 ≤ q) (hs : 0 ≤ s)
    (hB : ((B-1:ℕ):ℝ) ≤ s) (G : SimpleGraph V) (S : Fin N→Finset V)
    (family : Fin N→Set (SimpleGraph V))
    (hinter : ∀ i j,i≠j → ((S i∩S j).card:ℝ) ≤ q*t)
    (hmem : ∀ v,((Finset.univ.filter (fun i=>v∈S i)).card:ℝ) ≤ M)
    (hsmall : selectionPotential (graphSelectionActive S) q 0 (fun _=>0) < (2:ℝ)^B)
    (hcandidates : ∀ i,∀ J : SimpleGraph V,J ≤ spanningRestriction G (S i) →
      (∀ v,(J.degree v:ℝ) ≤ D*s) →
      ∃ C : Fin t→SimpleGraph V,
        (∀ a,C a∈family i ∧ C a ≤ spanningRestriction G (S i) ∧
          (∀ v,(C a).degree v ≤ D) ∧ Disjoint (C a) J) ∧
        (∀ a b,a≠b → Disjoint (C a) (C b))) :
    ∃ F : Fin N→SimpleGraph V,
      (∀ i,F i∈family i ∧ F i ≤ spanningRestriction G (S i) ∧ ∀ v,(F i).degree v ≤ D) ∧
      (∀ i j,i≠j → Disjoint (F i) (F j)) ∧
      ∀ v,((⨆ i,F i).degree v:ℝ) ≤ D*M := by
  letI : Nonempty (Fin t) := Fin.pos_iff_nonempty.mp ht
  let allowed := fun i (C : SimpleGraph V)=>C∈family i ∧ C ≤ G ∧ GraphSupportedOn (S i) C ∧ ∀ v,C.degree v ≤ D
  obtain ⟨F,hF,hdisj,hcounts⟩ := sequential_select_bounded_hits (A:=Fin t) B
    (graphSelectionActive S) (graphSelectionHit S) allowed Disjoint (⊥ : SimpleGraph V)
    (graphSelectionHit_bot S) q hq hsmall (by
      intro i F hprefix hsafe
      have hsup (j : Fin N) : GraphSupportedOn (S j) (F j) := by
        by_cases hj : j.val < i.val
        · exact (hprefix.2.1 j hj).2.2.1
        · rw [hprefix.1 j (by omega)]
          intro v w h;exact h.elim
      have hdeg (j : Fin N) (v : V) : (F j).degree v ≤ D := by
        by_cases hj : j.val < i.val
        · exact (hprefix.2.1 j hj).2.2.2 v
        · rw [hprefix.1 j (by omega)];simp
      have hleG (j : Fin N) : F j ≤ G := by
        by_cases hj : j.val < i.val
        · exact (hprefix.2.1 j hj).2.1
        · rw [hprefix.1 j (by omega)];exact bot_le
      let J := spanningRestriction (⨆ j,F j) (S i)
      have hJG : J ≤ spanningRestriction G (S i) := by
        intro v w h
        obtain ⟨hvw,hv,hw⟩ := (spanningRestriction_adj _ _ _ _).mp h
        obtain ⟨j,hj⟩ := SimpleGraph.iSup_adj.mp hvw
        exact (spanningRestriction_adj _ _ _ _).mpr ⟨hleG j hj,hv,hw⟩
      have hJD (v : V) : (J.degree v:ℝ) ≤ D*s := by
        rw [show J=spanningRestriction (⨆ j,F j) (S i) from rfl,spanningRestriction_degree]
        by_cases hv : v∈S i
        · rw [if_pos hv]
          let x : SelectionVertexTest S := ⟨(i,v),hv⟩
          have he := graphSelection_counter_eq S F x (fun j hj=>hprefix.1 j hj) hsup
          have hb := graph_iSup_local_degree_bound F (S i) v D (fun j=>hdeg j v)
          rw [show (Finset.univ.filter (fun j=>∃ w∈S i,(F j).Adj v w)).card=
            selectionCounter (graphSelectionActive S) (graphSelectionHit S) F x from he] at hb
          have hcount : selectionCounter (graphSelectionActive S) (graphSelectionHit S) F x ≤ B-1 := by
            have hh:=hsafe x;omega
          have hb' := hb.trans (Nat.mul_le_mul_left D hcount)
          have hreal : (((⨆ j,F j).neighborFinset v∩S i).card:ℝ) ≤ D*((B-1:ℕ):ℝ) := by exact_mod_cast hb'
          exact hreal.trans (mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg _))
        · rw [if_neg hv]
          exact_mod_cast (mul_nonneg (Nat.cast_nonneg D) hs)
      obtain ⟨C,hC,hCdisj⟩ := hcandidates i J hJG hJD
      have hCs (a : Fin t) : GraphSupportedOn (S i) (C a) := by
        intro v w h
        exact ((spanningRestriction_adj G (S i) v w).mp ((hC a).2.1 h)).2
      refine ⟨C,?_,?_,?_⟩
      · intro a
        exact ⟨(hC a).1,((hC a).2.1.trans (spanningRestriction_le G (S i))),hCs a,(hC a).2.2.1⟩
      · intro a j hj
        exact disjoint_of_restricted_union F (S i) (C a) (hCs a) (hC a).2.2.2 j
      · intro x hx
        have hix : i≠x.val.1 := by intro he;rw [he] at hx;exact (Nat.lt_irrefl _ hx.1)
        have hh := graph_candidates_hit_bound (S i) (S x.val.1) x.val.2 C hCs hCdisj
        have hh' : ((Finset.univ.filter (fun a=>graphSelectionHit S x (C a))).card:ℝ) ≤ (S i∩S x.val.1).card := by
          unfold graphSelectionHit
          have hhR : ((Finset.univ.filter (fun a=>∃ w∈S x.val.1,(C a).Adj x.val.2 w)).card:ℝ) ≤ (S i∩S x.val.1).card := by exact_mod_cast hh
          convert hhR using 1 <;> congr!
        simpa only [Fintype.card_fin] using hh'.trans (hinter i x.val.1 hix))
  refine ⟨F,?_,?_,?_⟩
  · intro i
    refine ⟨(hF i).1,?_,(hF i).2.2.2⟩
    intro v w h
    exact (spanningRestriction_adj _ _ _ _).mpr ⟨(hF i).2.1 h,(hF i).2.2.1 v w h⟩
  · intro i j hij
    rcases lt_or_gt_of_ne hij with h|h
    · exact hdisj i j h
    · exact (hdisj j i h).symm
  · intro v
    have hh := graph_iSup_global_degree_bound F S D (fun i=>(hF i).2.2.1) (fun i=>(hF i).2.2.2) v
    have hh' : ((⨆ i,F i).degree v:ℝ) ≤ D*((Finset.univ.filter (fun i=>v∈S i)).card:ℝ) := by exact_mod_cast hh
    exact hh'.trans (mul_le_mul_of_nonneg_left (hmem v) (Nat.cast_nonneg _))

end Oberwolfach
