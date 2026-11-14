module

public import Oberwolfach.SparseGreedySequences

@[expose] public section

/-! Ordered embeddings of a finite graph from common-neighbour counts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {K : ℕ}

def finitePatternRequirements (G : SimpleGraph (Fin K)) (n : ℕ) (f : Fin n→V) : Finset V :=
  if h : n<K then (Finset.univ.filter (fun i : Fin n=>G.Adj ⟨i.val,lt_trans i.isLt h⟩ ⟨n,h⟩)).image f else ∅

theorem finitePatternRequirements_card (G : SimpleGraph (Fin K)) (n : ℕ) (f : Fin n→V)
    (h : n<K) : (finitePatternRequirements G n f).card≤G.degree ⟨n,h⟩ := by
  rw [finitePatternRequirements,dif_pos h]
  apply Finset.card_image_le.trans
  let e : Fin n ↪ Fin K := ⟨fun i=>⟨i.val,lt_trans i.isLt h⟩,by intro i j he;exact Fin.ext (congrArg (fun i : Fin K=>i.val) he)⟩
  have hi : (Finset.univ.filter (fun i : Fin n=>G.Adj (e i) ⟨n,h⟩)).image e ⊆ G.neighborFinset ⟨n,h⟩ := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    exact (G.mem_neighborFinset _ _).mpr (Finset.mem_filter.mp hi).2.symm
  have hh := Finset.card_le_card hi
  rw [Finset.card_image_of_injective _ e.injective,SimpleGraph.card_neighborFinset_eq_degree] at hh
  exact hh

theorem finitePatternGood_adj (Q F : SimpleGraph V) (A W : Finset V)
    (G : SimpleGraph (Fin K)) (f : Fin K→V)
    (hf : SparseGreedyGood Q F A W (finitePatternRequirements G) f)
    (i j : Fin K) (hij : G.Adj i j) : Q.Adj (f i) (f j) := by
  have hordered (i j : Fin K) (hlt : i.val<j.val) (hadj : G.Adj i j) : Q.Adj (f i) (f j) := by
    apply hf.2.2.2.2 j
    rw [finitePatternRequirements,dif_pos j.isLt]
    refine Finset.mem_image.mpr ⟨⟨i.val,hlt⟩,?_,?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hadj⟩
    · rfl
  rcases lt_or_gt_of_ne (show i.val≠j.val from fun h=>hij.ne (Fin.ext h)) with h|h
  · exact hordered i j h hij
  · exact (hordered j i h hij.symm).symm

theorem finite_pattern_count (Q F : SimpleGraph V) (A W : Finset V)
    (G : SimpleGraph (Fin K)) (h : ℕ) (L b a : ℝ)
    (hL : 0≤L) (ha : 0≤a) (hF : ∀ v,(F.degree v:ℝ)≤L)
    (hbudget : a≤b-((W.card:ℝ)+K)*(L+1))
    (hdeg : ∀ i,G.degree i≤h)
    (hcommon : ∀ R : Finset V,R.card≤h → b≤((common A R (fun x=>Q.neighborFinset x)).card:ℝ)) :
    a^K≤(Fintype.card {f : Fin K→V // SparseGreedyGood Q F A W (finitePatternRequirements G) f}:ℝ) := by
  apply sparse_greedy_sequence_count Q F A W (finitePatternRequirements G) K L b a hL ha hF hbudget
  intro n hn f _
  exact hcommon _ ((finitePatternRequirements_card G n f hn).trans (hdeg _))

end Oberwolfach
