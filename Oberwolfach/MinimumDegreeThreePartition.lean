module

public import Oberwolfach.GraphPartitionGood
public import Oberwolfach.PartitionFailureScale

@[expose] public section

/-! A balanced three-part partition retaining minimum degree above three
quarters in every part. The original graph need not be nearly regular. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem minimum_degree_three_partition (α : ℝ) (hα : 0<α) :
    ∃ N : ℕ,∀ (V : Type) [Fintype V],N≤Fintype.card V → 3∣Fintype.card V →
      ∀ G : SimpleGraph V,(∀ v,(3/4+α)*Fintype.card V≤(G.degree v:ℝ)) →
      ∃ m : ℕ,∃ P : FixedPartition V 3 (fun _=>m),
        Fintype.card V=3*m ∧ ∀ v i,(3/4:ℝ)*m≤graphCellDegree G (Equiv.refl V) P v i := by
  let η := α/2
  have hη : 0<η := by dsimp [η];positivity
  obtain ⟨N,hN⟩ := partition_failure_eventually_small 3 (by norm_num) η hη
  refine ⟨max N 2,?_⟩
  intro V _ hn hdiv G hdeg
  have hn2 : 2≤Fintype.card V := (le_max_right N 2).trans hn
  have hnpos : (0:ℝ)<Fintype.card V := by exact_mod_cast (show 0<Fintype.card V by omega)
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨m,hnm⟩ := hdiv
  have hm : 0<m := by omega
  have hmR : (0:ℝ)<m := Nat.cast_pos.mpr hm
  have hnmR : (Fintype.card V:ℝ)=3*m := by exact_mod_cast hnm
  letI : Nonempty (FixedPartition V 3 (fun _=>m)) := fixedPartition_nonempty _ (by simpa using hnm.symm)
  let μ := FiniteLaw.uniform (FixedPartition V 3 (fun _=>m))
  let Bad := fun z : Fin 3×V=>fun P : FixedPartition V 3 (fun _=>m)=>
    η*m≤|(graphCellDegree G (Equiv.refl V) P z.2 z.1:ℝ)-(G.degree z.2)*(m/(Fintype.card V:ℝ))|
  let p := 2*Real.exp (-η^2*m/2)
  have htail (z : Fin 3×V) : μ.probability (Bad z)≤p := by
    exact graphPartition_degree_tail G (Equiv.refl V) z.2 z.1 m hm rfl _ 0 η hη
      (by positivity) (by simp)
  have hsum : ∑ _z : Fin 3×V,p<1 := by
    have hf := (hN _ ((le_max_left N 2).trans hn)).2.2
    have hd : Fintype.card V/3=m := by rw [hnm];omega
    rw [partitionFailure,hd] at hf
    have hinv : 1/(Fintype.card V:ℝ)<1 := (div_lt_one hnpos).mpr (by exact_mod_cast hn2)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat,nsmul_eq_mul]
    dsimp [p]
    have he : 0≤Real.exp (-η^2*m/2) := (Real.exp_pos _).le
    nlinarith only [hf,hinv,mul_nonneg (Nat.cast_nonneg (Fintype.card V)) he]
  obtain ⟨P,_,hP⟩ := finiteLaw_common_event_exists μ Finset.univ Bad (fun _=>p)
    (fun z _=>htail z) hsum
  refine ⟨m,P,hnm,?_⟩
  intro v i
  have hg := lt_of_not_ge (hP (i,v) (Finset.mem_univ _))
  change |(graphCellDegree G (Equiv.refl V) P v i:ℝ)-(G.degree v)*(m/(Fintype.card V:ℝ))|<η*m at hg
  have hmean : (3/4+α)*m≤(G.degree v)*(m/(Fintype.card V:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_right (hdeg v) (by positivity : (0:ℝ)≤m/(Fintype.card V:ℝ))
    have he : ((3/4+α)*Fintype.card V)*(m/(Fintype.card V:ℝ))=(3/4+α)*m := by field_simp
    rwa [he] at hh
  have hl := (abs_lt.mp hg).1
  dsimp [η] at hl
  nlinarith only [hl,hmean,mul_pos hα hmR]

end Oberwolfach
