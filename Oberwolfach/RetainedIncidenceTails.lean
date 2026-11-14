module

public import Oberwolfach.RetainedIncidenceSets
public import Oberwolfach.LocalFilterConcentration

@[expose] public section

/-! Size, overlap and membership tails for physical-coordinate incidence
sets. Independence is used only between the coordinate sets of distinct
outside indices, never between the three resulting families of events. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V J E:Type*} [Fintype V] [Fintype J] [Fintype E]
  [DecidableEq V] [DecidableEq J] [DecidableEq E]

theorem univ_filter_both_memberships (A B:Finset V)
    [DecidablePred (fun v=>v∈A∧v∈B)]:
    Finset.univ.filter (fun v=>v∈A∧v∈B)=A∩B := by ext;simp

theorem finiteLaw_upper_deviation {Ω:Type*} [Fintype Ω] (μ:FiniteLaw Ω) (X:Ω→ℝ)
    (a t err:ℝ) (hmean:μ.expectation X≤a)
    (htail:μ.probability (fun σ=>t≤|X σ-μ.expectation X|)≤err):
    μ.probability (fun σ=>a+t≤X σ)≤err := by
  apply (finiteLaw_probability_mono μ _ _ ?_).trans htail
  intro σ hσ
  have hh:=le_abs_self (X σ-μ.expectation X)
  linarith

theorem retainedIncidenceSet_row_tail (C:J→V→Finset E) (j:J)
    (p:ℝ) (hp:0≤p) (hp1:p≤1) (M n:ℝ) (hM:0<M) (hn:0<n)
    (hsize:(Fintype.card V:ℝ)≤n)
    (hread:∀ v,((C j v).card:ℝ)≤M)
    (haffect:∀ e,((Finset.univ.filter (fun v=>e∈C j v)).card:ℝ)≤M)
    (t:ℝ) (ht:0<t):
    (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1)).probability
      (fun σ=>p*M*Fintype.card V+t≤((retainedIncidenceSet C σ j).card:ℝ))≤
      2*Real.exp (-2*t^2/((2*M)^2*n)) := by
  have he (σ:E→Bool):
      Finset.univ.filter (fun v=>v∈retainedIncidenceSet C σ j)=retainedIncidenceSet C σ j := by ext;simp
  have hh:=finiteLaw_local_filter_tail (fun _:E=>FiniteLaw.retentionCoin p hp hp1)
    (fun σ v=>v∈retainedIncidenceSet C σ j) (C j) (retainedIncidenceSet_local C j)
    (2*M) n (by positivity) hn hsize (fun v=>(hread v).trans (by linarith))
    (fun e=>(haffect e).trans (by linarith)) t ht
  simp only [Finset.filter_and,Finset.filter_mem_eq_inter,Finset.univ_inter] at hh
  exact finiteLaw_upper_deviation _ _ _ _ _ (retainedIncidenceSet_row_mean C j p hp hp1 M hread) hh

theorem retainedIncidenceSet_pair_tail (C:J→V→Finset E) (i j:J)
    (hd:∀ v,Disjoint (C i v) (C j v))
    (p:ℝ) (hp:0≤p) (hp1:p≤1) (M n:ℝ) (hM:0<M) (hn:0<n)
    (hsize:(Fintype.card V:ℝ)≤n)
    (hread:∀ k v,((C k v).card:ℝ)≤M)
    (haffect:∀ k e,((Finset.univ.filter (fun v=>e∈C k v)).card:ℝ)≤M)
    (t:ℝ) (ht:0<t):
    (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1)).probability
      (fun σ=>p^2*M^2*Fintype.card V+t≤((retainedIncidenceSet C σ i∩retainedIncidenceSet C σ j).card:ℝ))≤
      2*Real.exp (-2*t^2/((2*M)^2*n)) := by
  let S:V→Finset E:=fun v=>C i v∪C j v
  have hr (v:V):((S v).card:ℝ)≤2*M := by
    have hh:((S v).card:ℝ)≤(C i v).card+(C j v).card:=by exact_mod_cast Finset.card_union_le (C i v) (C j v)
    linarith [hread i v,hread j v]
  have ha (e:E):((Finset.univ.filter (fun v=>e∈S v)).card:ℝ)≤2*M := by
    have he:Finset.univ.filter (fun v=>e∈S v)=
        (Finset.univ.filter (fun v=>e∈C i v))∪(Finset.univ.filter (fun v=>e∈C j v)) := by ext;simp [S]
    rw [he]
    have hh:=Finset.card_union_le (Finset.univ.filter (fun v=>e∈C i v))
      (Finset.univ.filter (fun v=>e∈C j v))
    have hh':(((Finset.univ.filter (fun v=>e∈C i v))∪(Finset.univ.filter (fun v=>e∈C j v))).card:ℝ)≤
      (Finset.univ.filter (fun v=>e∈C i v)).card+(Finset.univ.filter (fun v=>e∈C j v)).card:=by exact_mod_cast hh
    linarith [haffect i e,haffect j e]
  have he (σ:E→Bool):Finset.univ.filter
      (fun v=>v∈retainedIncidenceSet C σ i∧v∈retainedIncidenceSet C σ j)=
      retainedIncidenceSet C σ i∩retainedIncidenceSet C σ j := by ext;simp
  have hh:=finiteLaw_local_filter_tail (fun _:E=>FiniteLaw.retentionCoin p hp hp1)
    (fun σ v=>v∈retainedIncidenceSet C σ i∧v∈retainedIncidenceSet C σ j) S
    (fun v σ τ hagree=>and_congr
      (retainedIncidenceSet_local C i v σ τ (fun e he=>hagree e (Finset.mem_union_left _ he)))
      (retainedIncidenceSet_local C j v σ τ (fun e he=>hagree e (Finset.mem_union_right _ he))))
    (2*M) n (by positivity) hn hsize hr ha t ht
  simp only [univ_filter_both_memberships] at hh
  exact finiteLaw_upper_deviation _ _ _ _ _
    (retainedIncidenceSet_pair_mean C i j hd p hp hp1 M hM.le (hread i) (hread j)) hh

theorem retainedIncidenceSet_membership_tail (C:J→V→Finset E) (v:V)
    (hd:∀ i j,i≠j→Disjoint (C i v) (C j v))
    (p:ℝ) (hp:0≤p) (hp1:p≤1) (M n:ℝ) (hM:1≤M) (hn:0<n)
    (hsize:(Fintype.card J:ℝ)≤n) (hread:∀ i,((C i v).card:ℝ)≤M)
    (t:ℝ) (ht:0<t):
    (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1)).probability
      (fun σ=>p*M*Fintype.card J+t≤((Finset.univ.filter (fun i=>v∈retainedIncidenceSet C σ i)).card:ℝ))≤
      2*Real.exp (-2*t^2/((2*M)^2*n)) := by
  let C':Unit→J→Finset E:=fun _ i=>C i v
  have ha (e:E):((Finset.univ.filter (fun i=>e∈C' () i)).card:ℝ)≤M := by
    have hh:(Finset.univ.filter (fun i=>e∈C' () i)).card≤1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      by_contra hij
      exact Finset.disjoint_left.mp (hd i j hij) (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
    exact (by exact_mod_cast hh : ((Finset.univ.filter (fun i=>e∈C' () i)).card:ℝ)≤1).trans hM
  have he (σ:E→Bool):retainedIncidenceSet C' σ ()=
      Finset.univ.filter (fun i=>v∈retainedIncidenceSet C σ i) := by ext;simp [C']
  have hh:=retainedIncidenceSet_row_tail C' () p hp hp1 M n (by linarith) hn hsize hread ha t ht
  simpa only [he] using hh

end Oberwolfach
