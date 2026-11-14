module

public import Oberwolfach.OrdinaryCommonPathCycles
public import Oberwolfach.PairedAbsorberCounts

@[expose] public section

/-! Actual paired ordinary absorbers from the supplied sparse
common-neighbourhood bounds. No independence condition is imposed on the
prescribed root set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
set_option synthInstance.maxSize 256
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ}

def ordinaryLocalCountCoeff (m : ℕ) (γ : ℝ) : ℝ := min ((γ/2)^(m+1)) ((γ/2)^m)

theorem ordinaryLocalCountCoeff_pos (m : ℕ) (γ : ℝ) (hγ : 0<γ) :
    0<ordinaryLocalCountCoeff m γ := by unfold ordinaryLocalCountCoeff;positivity

theorem ordinary_local_paired_absorber_count (Q F : SimpleGraph V) (T : Finset V)
    (hm : 2≤m) (γ L : ℝ) (hγ : 0<γ) (hL : 0≤L)
    (hF : ∀ v,(F.degree v:ℝ)≤L)
    (hcommon : ∀ S : Finset V,S.card≤(if m=2 then 3 else 2) →
      γ*Fintype.card V≤((common T S (fun x=>Q.neighborFinset x)).card:ℝ))
    (hbudget : (m+3:ℝ)*(L+1)≤γ/2*Fintype.card V)
    (hnb : 2*(m+1:ℝ)^2≤ordinaryLocalCountCoeff m γ*Fintype.card V)
    (hnp : 2*(m:ℝ)*(2*(m+1)+(m+1)*m)≤ordinaryLocalCountCoeff m γ*Fintype.card V)
    (x : Fin (m+1)→V) (hx : Function.Injective x) (hxT : ∀ i,x i∈T) :
    (ordinaryLocalCountCoeff m γ/2)^(m+2)*(Fintype.card V:ℝ)^((m+1)*(m+1))≤
      Fintype.card (LabelledCycleRecord (localOrdinaryVertices (Q:=Q) (F:=F) (T:=T) (r:=m+1))
        (pairedAbsorberTemplate (m+1)).val (Finset.univ.image x)) := by
  let n : ℝ := Fintype.card V
  let a := γ/2*n
  let β := ordinaryLocalCountCoeff m γ
  let Base := fun f : Fin (m+1)→V => SparseGreedyGood Q F T ∅
    (finitePatternRequirements (SimpleGraph.cycleGraph (m+1))) f
  let Path := fun y : Fin (m+1)→V => fun i : ℕ => fun f : Fin m→V =>
    ∃ h : i<m+1,SparseGreedyGood Q F T {x ⟨i,h⟩,y ⟨i,h⟩}
      (ordinaryPathRequirements m (x ⟨i,h⟩) (y ⟨i,h⟩)) f
  have ha : 0≤a := by dsimp [a,n];positivity
  have hbase0 := finite_pattern_count Q F T ∅ (SimpleGraph.cycleGraph (m+1)) 2 L
    (γ*n) a hL ha hF (by
      have hh := mul_le_mul_of_nonneg_right (show (m+1:ℝ)≤m+3 by linarith) (show 0≤L+1 by linarith)
      simp only [Finset.card_empty,Nat.cast_zero,zero_add,Nat.cast_add,Nat.cast_one]
      dsimp [a];linarith)
    (fun i=>by convert (cycleGraph_regular (show 3≤m+1 by omega) i).le using 1 <;> congr!)
    (fun S hS=>hcommon S (hS.trans (by split_ifs <;> omega)))
  have hbase : β*n^(m+1)≤Fintype.card {f // Base f} := by
    have hh := mul_le_mul_of_nonneg_right (min_le_left ((γ/2)^(m+1)) ((γ/2)^m))
      (pow_nonneg (show 0≤n by dsimp [n];positivity) (m+1))
    have he : a^(m+1)=(γ/2)^(m+1)*n^(m+1) := mul_pow _ _ _
    exact hh.trans (he ▸ hbase0)
  have hpath (y : Fin (m+1)→V) (i : ℕ) (hi : i<m+1) :
      β*n^m≤Fintype.card {f // Path y i f} := by
    let W : Finset V := {x ⟨i,hi⟩,y ⟨i,hi⟩}
    let R := ordinaryPathRequirements m (x ⟨i,hi⟩) (y ⟨i,hi⟩)
    have hW : (W.card:ℝ)≤2 := by exact_mod_cast (Finset.card_le_two : W.card≤2)
    have hh := sparse_greedy_sequence_count Q F T W R m L (γ*n) a hL ha hF (by
      have hl := mul_le_mul_of_nonneg_right (show (W.card:ℝ)+m≤m+3 by linarith) (show 0≤L+1 by linarith)
      dsimp [a];linarith)
      (fun j _ f _=>hcommon _ (ordinaryPathRequirements_card m _ _ j f))
    have hβ := mul_le_mul_of_nonneg_right (min_le_right ((γ/2)^(m+1)) ((γ/2)^m))
      (pow_nonneg (show 0≤n by dsimp [n];positivity) m)
    have he : a^m=(γ/2)^m*n^m := mul_pow _ _ _
    have hc : β*n^m≤Fintype.card {f // SparseGreedyGood Q F T W R f} := hβ.trans (he ▸ hh)
    have heP : Path y i=SparseGreedyGood Q F T W R := by
      funext f
      apply propext
      constructor
      · rintro ⟨hi',hf⟩;exact hf
      · intro hf;exact ⟨hi,hf⟩
    have hcard := Fintype.card_congr (Equiv.subtypeEquivRight (fun f=>Iff.of_eq (congrFun heP f)))
    exact hc.trans_eq (by exact_mod_cast hcard.symm)
  apply paired_absorber_abundance (localOrdinaryVertices (Q:=Q) (F:=F) (T:=T) (r:=m+1)) (by omega)
    x hx Base Path β (ordinaryLocalCountCoeff_pos m γ hγ)
    (fun y hy=>hy.1) (fun y hy=>ordinary_base_tuple_cycle Q F T (by omega) y hy)
    (fun y hy _ i f hf=>?_) (fun y _ _ i _ f hf=>?_) hbase (fun y _ _ i hi=>by convert hpath y i hi using 1 <;> congr!) hnb hnp
  · obtain ⟨hi,hf⟩ := hf
    constructor
    · exact ordinary_common_path_cycle Q F T hm (x i) (y i) (y i) (Or.inr rfl) (hy.2.1 i).1 f hf
    · exact ordinary_common_path_cycle Q F T hm (x i) (y i) (x i) (Or.inl rfl) (hxT i) f hf
  · obtain ⟨hi,hf⟩ := hf
    exact hf.1

end Oberwolfach
