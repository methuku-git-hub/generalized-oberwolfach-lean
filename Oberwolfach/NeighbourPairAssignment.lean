module

public import Oberwolfach.DegreeCutMatchingDeletion
public import Oberwolfach.BipartiteBalancedSplit
public import Oberwolfach.BipartiteRelationEmbedding

@[expose] public section

/-! Assign two distinct row neighbours to each column, covering every row
once and avoiding a fixed graph of bounded maximum degree. This is the
source lemma `lem:pr:ordinary-endpoints`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem neighbour_pairs_from_balanced_split {X Y : Type} [Fintype X] [Fintype Y]
    (m : ℕ) (hm : 0<m) (hY : Fintype.card Y=m)
    (E : X→Y→Prop) (F : SimpleGraph X) (lam b : ℝ)
    (hlam : 0<lam) (hb : 0≤b) (hsmall : b≤lam*m/4)
    (hmargin : b<lam^2*m/16)
    (P : FixedPartition X 2 (fun _=>m))
    (hrow : ∀ x,lam*m≤((Finset.univ.filter (E x)).card:ℝ))
    (hcol : ∀ y i,lam*m/2≤(((Finset.univ.filter (fun x=>E x y))∩(fixedPartitionCell P i).val).card:ℝ))
    (hF : ∀ x,(F.degree x:ℝ)≤b)
    (hcut : ∀ S : Finset X,∀ T : Finset Y,lam/16*m≤(S.card:ℝ) → lam/16*m≤(T.card:ℝ) →
      lam*S.card*T.card≤(bipartiteMatrixCut (fun x y=>if E x y then 1 else 0) S T:ℝ)) :
    ∃ v w : Y↪X,(∀ y,E (v y) y∧E (w y) y∧¬F.Adj (v y) (w y)) ∧
      Disjoint (Set.range v) (Set.range w) ∧ (∀ x,(∃ y,v y=x)∨∃ y,w y=x) := by
  classical
  have hmR : (0:ℝ)<m:=Nat.cast_pos.mpr hm
  let f (i:Fin 2):Fin m↪X:=partitionCellEmbedding P i m rfl
  have hcell (i:Fin 2) (y:Y) : lam*m/2≤((Finset.univ.filter (fun j=>E (f i j) y)).card:ℝ):=by
    rw [show (Finset.univ.filter (fun j=>E (f i j) y)).card=
      ((Finset.univ.filter (fun x=>E x y))∩(fixedPartitionCell P i).val).card from partition_cell_predicate_card P i (fun x=>E x y)]
    exact hcol y i
  have hcut' (i:Fin 2) (S:Finset (Fin m)) (T:Finset Y)
      (hS : lam*m/4≤(S.card:ℝ)) (hT : lam*m/4≤(T.card:ℝ)) :
      lam*S.card*T.card≤(bipartiteMatrixCut (fun j y=>if E (f i j) y then 1 else 0) S T:ℝ):=by
    rw [bipartite_cut_embedding (f i) (fun x y=>if E x y then 1 else 0) S T]
    have hh:=hcut (S.map (f i)) T (by simp only [Finset.card_map];nlinarith only [hS,mul_pos hlam hmR]) (by nlinarith only [hT,mul_pos hlam hmR])
    simpa only [Finset.card_map] using hh
  have hcard : Fintype.card (Fin m)=Fintype.card Y:=by simp [hY]
  obtain ⟨σ,hσ⟩:=degree_cut_matching_after_deletion (fun j y=>E (f 0 j) y) (fun _ _=>False)
    hcard (lam*m/4) 0 lam (by positivity) (by norm_num) hlam (by positivity)
    (fun j=>by have hh:=hrow (f 0 j);linarith only [hh,mul_pos hlam hmR])
    (fun y=>by have hh:=hcell 0 y;linarith only [hh,mul_pos hlam hmR])
    (by intro j;simp) (by intro y;simp) (hcut' 0)
  let v : Y↪X:=σ.symm.toEmbedding.trans (f 0)
  have hv (y:Y):E (v y) y:=by simpa [v] using (hσ (σ.symm y)).1
  let J (j:Fin m) (y:Y):=F.Adj (v y) (f 1 j)
  have hjrow (j:Fin m) : ((Finset.univ.filter (J j)).card:ℝ)≤b:=by
    have hh:=embedding_predicate_card v (fun x=>F.Adj (f 1 j) x)
    have he : (Finset.univ.filter (J j)).card=(Finset.univ.filter (fun y=>F.Adj (f 1 j) (v y))).card:=by
      congr 1;ext y;simp only [Finset.mem_filter,Finset.mem_univ,true_and,J];exact F.adj_comm _ _
    rw [he]
    have hn : (Finset.univ.filter (fun x=>F.Adj (f 1 j) x)).card=F.degree (f 1 j):=by
      rw [SimpleGraph.degree];congr 1;ext x;simp
    rw [hn] at hh
    exact (Nat.cast_le.mpr hh).trans (hF _)
  have hjcol (y:Y) : ((Finset.univ.filter (fun j=>J j y)).card:ℝ)≤b:=by
    have hh:=embedding_predicate_card (f 1) (fun x=>F.Adj (v y) x)
    have hn : (Finset.univ.filter (fun x=>F.Adj (v y) x)).card=F.degree (v y):=by
      rw [SimpleGraph.degree];congr 1;ext x;simp
    rw [hn] at hh
    exact (Nat.cast_le.mpr hh).trans (hF _)
  have hmarg : b<lam*(lam*m/4):=by nlinarith only [hmargin,mul_pos (sq_pos_of_pos hlam) hmR]
  obtain ⟨τ,hτ⟩:=degree_cut_matching_after_deletion (fun j y=>E (f 1 j) y) J
    hcard (lam*m/4) b lam (by positivity) hb hlam hmarg
    (fun j=>by have hh:=hrow (f 1 j);linarith only [hh,hsmall,mul_pos hlam hmR])
    (fun y=>by have hh:=hcell 1 y;linarith only [hh,hsmall]) hjrow hjcol (hcut' 1)
  let w : Y↪X:=τ.symm.toEmbedding.trans (f 1)
  have hw (y:Y):E (w y) y∧¬F.Adj (v y) (w y):=by simpa [w,J] using hτ (τ.symm y)
  refine ⟨v,w,fun y=>⟨hv y,(hw y).1,(hw y).2⟩,?_,?_⟩
  · apply Set.disjoint_left.mpr
    rintro x ⟨y,rfl⟩ ⟨z,hz⟩
    have h0 : P.val (v y)=0:=partitionCellEmbedding_colour P 0 m rfl (σ.symm y)
    have h1 : P.val (w z)=1:=partitionCellEmbedding_colour P 1 m rfl (τ.symm z)
    rw [hz,h0] at h1
    exact (by decide : (0:Fin 2)≠1) h1
  · intro x
    have hcases : P.val x=0∨P.val x=1:=by omega
    rcases hcases with h0|h1
    · obtain ⟨j,hj⟩:=(partitionCellEmbedding_range P 0 m rfl x).mpr h0
      exact Or.inl ⟨σ j,by simpa [v,f] using hj⟩
    · obtain ⟨j,hj⟩:=(partitionCellEmbedding_range P 1 m rfl x).mpr h1
      exact Or.inr ⟨τ j,by simpa [w,f] using hj⟩

theorem ordinary_neighbour_pair_assignment (lam : ℝ) (hlam : 0<lam) :
    ∀ b : ℕ,∃ N : ℕ,∀ (X Y : Type) [Fintype X] [Fintype Y],
      ∀ m : ℕ,N≤m → Fintype.card X=2*m → Fintype.card Y=m →
      ∀ (E : X→Y→Prop) (F : SimpleGraph X),
      (∀ x,lam*m≤((Finset.univ.filter (E x)).card:ℝ)) →
      (∀ y,2*lam*m≤((Finset.univ.filter (fun x=>E x y)).card:ℝ)) →
      (∀ x,F.degree x≤b) →
      (∀ S : Finset X,∀ T : Finset Y,lam/16*m≤(S.card:ℝ) → lam/16*m≤(T.card:ℝ) →
        lam*S.card*T.card≤(bipartiteMatrixCut (fun x y=>if E x y then 1 else 0) S T:ℝ)) →
      ∃ v w : Y↪X,(∀ y,E (v y) y∧E (w y) y∧¬F.Adj (v y) (w y)) ∧
        Disjoint (Set.range v) (Set.range w) ∧ (∀ x,(∃ y,v y=x)∨∃ y,w y=x) := by
  intro b
  obtain ⟨N,hN⟩:=bipartite_balanced_split lam hlam
  obtain ⟨L,hL⟩:=exists_nat_gt (max (4*b/lam) (16*b/lam^2):ℝ)
  refine ⟨max N (max L 1),?_⟩
  intro X Y _ _ m hm hX hY E F hrow hcol hF hcut
  have hmpos : 0<m:=by omega
  have hLm : (L:ℝ)≤m:=Nat.cast_le.mpr (by omega)
  have hsmall : (b:ℝ)≤lam*m/4:=by
    have hh:4*b/lam<(m:ℝ):=(le_max_left _ _).trans_lt (hL.trans_le hLm)
    have hh':4*b<m*lam:=(div_lt_iff₀ hlam).mp hh
    nlinarith only [hh']
  have hmargin : (b:ℝ)<lam^2*m/16:=by
    have hh:16*b/lam^2<(m:ℝ):=(le_max_right _ _).trans_lt (hL.trans_le hLm)
    have hh':16*b<m*lam^2:=(div_lt_iff₀ (sq_pos_of_pos hlam)).mp hh
    nlinarith only [hh']
  obtain ⟨P,hP⟩:=hN X Y m ((le_max_left _ _).trans hm) hX hY E hcol
  exact neighbour_pairs_from_balanced_split m hmpos hY E F lam b hlam (by positivity) hsmall hmargin P
    hrow hP (fun x=>Nat.cast_le.mpr (hF x)) hcut

end Oberwolfach
