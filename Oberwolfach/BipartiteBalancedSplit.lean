module

public import Oberwolfach.GraphPartitionGood
public import Oberwolfach.PartitionFailureScale

@[expose] public section

/-! A balanced split of a row domain preserving all column degrees.
The columns may be outside the sampled domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem bipartite_balanced_split (lam : ℝ) (hlam : 0<lam) :
    ∃ N : ℕ,∀ (X Y : Type) [Fintype X] [Fintype Y],
      ∀ m : ℕ,N≤m → Fintype.card X=2*m → Fintype.card Y=m →
      ∀ E : X→Y→Prop,(∀ y,2*lam*m≤((Finset.univ.filter (fun x=>E x y)).card:ℝ)) →
      ∃ P : FixedPartition X 2 (fun _=>m),∀ y i,
        lam*m/2≤(((Finset.univ.filter (fun x=>E x y))∩(fixedPartitionCell P i).val).card:ℝ) := by
  obtain ⟨N,hN⟩:=partition_failure_eventually_small 2 (by norm_num) lam hlam
  refine ⟨max N 2,?_⟩
  intro X Y _ _ m hm hX hY E hdeg
  have hm2 : 2≤m:=(le_max_right N 2).trans hm
  have hmR : (0:ℝ)<m:=by exact_mod_cast (show 0<m by omega)
  letI : Nonempty (FixedPartition X 2 (fun _=>m)):=fixedPartition_nonempty _ (by simpa using hX.symm)
  let μ:=FiniteLaw.uniform (FixedPartition X 2 (fun _=>m))
  let A (y:Y):=Finset.univ.filter (fun x=>E x y)
  let Bad (z : Y×Fin 2) (P : FixedPartition X 2 (fun _=>m)):=
    lam*m/2≤|((A z.1∩(fixedPartitionCell P z.2).val).card:ℝ)-(A z.1).card/2|
  let p:=2*Real.exp (-lam^2*m/2)
  have htail (z:Y×Fin 2):μ.probability (Bad z)≤p:=by
    have ht:=fixedPartition_cell_count_tail (d:=fun _ : Fin 2=>m) z.2 (A z.1)
      (show (0:ℝ)≤lam*m/2 by positivity)
    have hmean : (m:ℝ)/Fintype.card X=1/2:=by rw [hX];push_cast;field_simp
    have hexp : -2*(lam*m/2)^2/(m:ℝ)=-lam^2*m/2:=by field_simp <;> ring
    simpa only [hmean,mul_one_div,hexp] using ht
  have hsum : ∑ _z:Y×Fin 2,p<1:=by
    have hf:=(hN (2*m) (by omega)).2.2
    have hd : 2*m/2=m:=by omega
    rw [partitionFailure,hd] at hf
    have hinv : 1/(2*m:ℝ)<1:=(div_lt_one (by positivity)).mpr (by exact_mod_cast (show 1<2*m by omega))
    have he : 0≤Real.exp (-lam^2*m/2):=(Real.exp_pos _).le
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,hY,Nat.cast_mul,Nat.cast_ofNat,nsmul_eq_mul]
    dsimp [p]
    push_cast at hf
    nlinarith only [hf,hinv,mul_nonneg (Nat.cast_nonneg m) he]
  obtain ⟨P,_,hP⟩:=finiteLaw_common_event_exists μ Finset.univ Bad (fun _=>p) (fun z _=>htail z) hsum
  refine ⟨P,?_⟩
  intro y i
  have hh:=lt_of_not_ge (hP (y,i) (Finset.mem_univ _))
  change |((A y∩(fixedPartitionCell P i).val).card:ℝ)-(A y).card/2|<lam*m/2 at hh
  have hl:=(abs_lt.mp hh).1
  have hg:=hdeg y
  change 2*lam*m≤((A y).card:ℝ) at hg
  dsimp only [A] at hl
  linarith

end Oberwolfach
