module

public import Oberwolfach.LongPreparationRetainedLengths
public import Oberwolfach.LongPreparationVertexFractions

@[expose] public section
/-! Classify a prescribed factor by a long-vertex majority or an abundant
short component length, as in the initial reduction. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_long_or_abundant_short {n:ℕ} (hn:0<n)
    (F:SimpleGraph (Fin n)) (hF:F.IsRegularOfDegree 2) (S:Set ℕ)
    (hS:AllowedCycleLengths F S) (K:ℕ) (hK:0<K):
    (1/2:ℝ)≤((Finset.univ.filter (fun v=>K<Fintype.card (F.connectedComponentMk v))).card:ℝ)/n ∨
    ∃ i:Fin K, (3 : ℕ) ≤ (i.val + 1) ∧ (i.val+1)∈S ∧
      (1/(2*(K:ℝ)):ℝ)≤
        ((Finset.univ.filter (fun v=>Fintype.card (F.connectedComponentMk v)=i.val+1)).card:ℝ)/n:=by
  let frac:=fun j:Option (Fin K)=>
    ((Finset.univ.filter (fun v=>longPreparationCycleClass F hF K v=j)).card:ℝ)/n
  have hfreq:=long_preparation_vertex_fractions (show 0<Fintype.card (Fin n) by simpa using hn) K (longPreparationCycleClass F hF K)
  have hsum:frac none+(∑ i,frac (some i))=1:=by simpa [frac] using hfreq.2
  have hlong:(Finset.univ.filter (fun v=>longPreparationCycleClass F hF K v=none))=
      (Finset.univ.filter (fun v=>K<Fintype.card (F.connectedComponentMk v))):=by
    apply Finset.filter_congr
    intro v _
    exact (long_preparation_cycle_class F hF K v).1
  by_cases hl:(1/2:ℝ)≤frac none
  · left
    simpa [frac,hlong] using hl
  · right
    have hK':(0:ℝ)<K:=by exact_mod_cast hK
    have ht0:0≤(1/(2*(K:ℝ)):ℝ):=by positivity
    have hex:∃ i:Fin K,(1/(2*(K:ℝ)):ℝ)≤frac (some i):=by
      by_contra h
      have hi (i:Fin K):frac (some i)≤1/(2*(K:ℝ)):=by
        exact (lt_of_not_ge (fun hh=>h ⟨i,hh⟩)).le
      have hsumupper:(∑ i:Fin K,frac (some i))≤(K:ℝ)*(1/(2*(K:ℝ))):=by
        calc
          _ ≤ ∑ _i:Fin K,(1/(2*(K:ℝ)):ℝ):=Finset.sum_le_sum (fun i _=>hi i)
          _ = _:=by simp
      have hone:(K:ℝ)*(1/(2*(K:ℝ)))=1/2:=by field_simp
      linarith
    obtain ⟨i,hi⟩:=hex
    have hi':(50:ℝ)/(100*(K:ℝ))≤
      ((Finset.univ.filter (fun v=>longPreparationCycleClass F hF K v=some i)).card:ℝ)/n:=by
      have heq:(50:ℝ)/(100*(K:ℝ))=1/(2*(K:ℝ)):=by field_simp; norm_num
      rw [heq]
      exact hi
    have hh:=long_preparation_retained_length_allowed hn F hF S hS K hK 50 (by norm_num) i hi'
    have hshort:(Finset.univ.filter (fun v=>longPreparationCycleClass F hF K v=some i))=
        (Finset.univ.filter (fun v=>Fintype.card (F.connectedComponentMk v)=i.val+1)):=by
      apply Finset.filter_congr
      intro v _
      exact (long_preparation_cycle_class F hF K v).2 i
    refine ⟨i,hh.1,hh.2.1,?_⟩
    simpa [frac,hshort] using hi
end Oberwolfach
