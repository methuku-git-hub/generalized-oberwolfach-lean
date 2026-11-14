module

public import Oberwolfach.VortexMarkedParentDegrees
public import Oberwolfach.SuccessorWeightFamilies
public import Oberwolfach.MarkedPhysicalDeletionRestriction

@[expose] public section

/-! Actual full vortex domains admit the separated positive successor
weights used in marked completion. All weights are chosen from the parent
graphs and permutations before any sampling marginals or outcomes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem vortex_full_successor_weight_families
    (k c : ℕ) (hlen : c+1=(k+2)*2) (α τ : ℝ) (hα : 0<α) (hτ : 0<τ)
    (hmargin : successorCycleRatio k+α/4≤1/2+α/2) :
    ∃ βmax : ℝ,0<βmax ∧ ∀ b : ℕ,∃ N : ℕ,1≤ N ∧
    ∀ (V U : Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (G : SimpleGraph V) (D m : ℕ) (β ε : ℝ) (Q : Vortex U G D β ε m),
    G.IsRegularOfDegree D → 0< Fintype.card V →
    (1/2+α)*Fintype.card V≤(D:ℝ) → 0< initialIndexDensity U D →
    0≤β → β≤βmax → 0<ε → ε≤1/4 → (N:ℝ)≤ε*m/2 →
    let A := fun i=>Q.vertices i
    let B := fun i=>Q.indices i;
    ∀ ρ : ∀ i,Equiv.Perm (A i),
    ∃ weight : ∀ i,(Fin (c+1)→A i)→ℝ,
      ∀ i≤ Q.length,SuccessorSequenceWeightConditions
        (G.comap (Subtype.val : A i→V)) (ρ i) b (2*(B i).card/initialIndexDensity U D) τ
        (successorWeightLower k (α/4)) (successorWeightUpper k (α/4)) (weight i) := by
  obtain ⟨δ,hδ,hweights⟩ := successor_sequence_weight_families k c hlen (α/4) τ (by positivity) hτ
  let βmax := min (α/8) (min (1/4) δ)
  have hbmax : 0<βmax := by dsimp [βmax];positivity
  refine ⟨βmax,hbmax,?_⟩
  intro b
  obtain ⟨N,hN,hweights⟩ := hweights b
  refine ⟨N,hN,?_⟩
  intro V U _ _ _ _ G D m β ε Q hreg hn hD hρ hb hbmax he he1 hsize A B ρ
  have hbα : β≤α/8 := hbmax.trans (min_le_left _ _)
  have hb1 : β≤1/4 := hbmax.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbδ : β≤δ := hbmax.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsz (i) (hi : i≤ Q.length) : N≤ Fintype.card (A i) := by
    rw [Fintype.card_coe]
    exact_mod_cast hsize.trans (Q.vertices_lower hi)
  have hstats (i) (hi : i≤ Q.length) (x : A i) :
      (A i).card/2≤2*(B i).card/initialIndexDensity U D ∧
      2*(B i).card/initialIndexDensity U D≤2*(A i).card ∧
      (1/2+α/2)*(A i).card≤(((G.comap (Subtype.val : A i→V)).degree x):ℝ) ∧
      |(((G.comap (Subtype.val : A i→V)).degree x):ℝ)-2*(B i).card/initialIndexDensity U D|≤β*(A i).card := by
    have hx : x.val∈Q.vertices (i-2) :=
      finset_chain_subset Q.vertices Q.length Q.nested (by omega : i-2≤ i) hi x.property
    have hh := Q.marked_parent_degrees hreg hn hD hα hρ hb hbα hb1 hi x.val hx
    let e : A i↪V := ⟨Subtype.val,Subtype.val_injective⟩
    have himage : Finset.univ.image e=A i := by
      ext v;simp only [Finset.mem_image,Finset.mem_univ,true_and,e,Function.Embedding.coeFn_mk];exact ⟨fun ⟨x,h⟩=>h ▸ x.property,fun h=>⟨⟨v,h⟩,rfl⟩⟩
    have heq := graph_comap_degree_into_image G e x
    rw [himage] at heq
    have heqr : (((G.comap (Subtype.val : A i→V)).degree x):ℝ)=((G.neighborFinset x.val∩A i).card:ℝ) := by exact_mod_cast heq
    rw [heqr]
    exact hh
  have hex (i) (hi : i≤ Q.length) : Nonempty (A i) :=
    Fintype.card_pos_iff.mp (lt_of_lt_of_le (by omega) (hsz i hi))
  apply hweights (fun i=>A i) (fun i=>G.comap (Subtype.val : A i→V)) ρ
    (fun i=>2*(B i).card/initialIndexDensity U D) Q.length hsz
  · intro i hi
    simpa only [Fintype.card_coe] using (hstats i hi (Classical.choice (hex i hi))).1
  · intro i hi
    simpa only [Fintype.card_coe] using (hstats i hi (Classical.choice (hex i hi))).2.1
  · intro i hi x
    apply (hstats i hi x).2.2.2.trans
    simpa only [Fintype.card_coe,mul_assoc] using mul_le_mul_of_nonneg_right hbδ (Nat.cast_nonneg (A i).card)
  · intro i hi x
    apply le_trans _ (hstats i hi x).2.2.1
    simpa only [Fintype.card_coe] using mul_le_mul_of_nonneg_right hmargin (Nat.cast_nonneg (A i).card)

end Oberwolfach
