module

public import Oberwolfach.BoundedGraphFractionalMatching
public import Oberwolfach.InducedFractionalCycles

@[expose] public section

/-! Bounded perfect fractional matching weights on an induced subset,
extended as a symmetric function on the actual ambient unordered pairs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem bounded_fractional_matching_on_subset (P:SimpleGraph V) (S:Finset V) (β:ℝ)
    (hβ:0<β) (hβhalf:β<1/2) (hn:4/β≤(S.card:ℝ))
    (hdeg:∀ v∈S,(1/2+β)*S.card≤((S∩P.neighborFinset v).card:ℝ)) :
    ∃ weight:Sym2 V→ℝ,
      (∀ v∈S,∀ w∈S,0≤weight s(v,w) ∧ weight s(v,w)≤5/(β*S.card)) ∧
      (∀ v∈S,∑ w∈S,weight s(v,w)=1) ∧
      (∀ v w,¬P.Adj v w → weight s(v,w)=0) ∧
      (∀ v∈S,∀ w∈S,P.Adj v w → β/(5*S.card)≤weight s(v,w)) := by
  obtain ⟨w,hsym,hzero,hbound,hsum⟩:=bounded_perfect_fractional_matching
    (P.induce (S:Set V)) β hβ hβhalf (by simpa using hn) (by
      intro v
      rw [induced_degree_intersection]
      simpa only [Finset.coe_sort_coe,Fintype.card_coe,Finset.inter_comm] using hdeg v.val v.property)
  let f:V→V→ℝ:=fun v u=>if hv:v∈S then if hu:u∈S then w ⟨v,hv⟩ ⟨u,hu⟩ else 0 else 0
  have hf (v u:V):f v u=f u v:=by
    by_cases hv:v∈S <;> by_cases hu:u∈S
    · simp only [f,dite_eq_left hv,dite_eq_left hu]
      exact hsym _ _
    all_goals simp [f,hv,hu]
  let weight:Sym2 V→ℝ:=Sym2.lift ⟨f,hf⟩
  have he (v u:V):weight s(v,u)=f v u:=rfl
  have hcard:(0:ℝ)<S.card:=(div_pos (by norm_num) hβ).trans_le hn
  refine ⟨weight,?_,?_,?_,?_⟩
  · intro v hv u hu
    rw [he]
    simp only [f,dite_eq_left hv,dite_eq_left hu]
    by_cases ha:P.Adj v u
    · have hb:=hbound ⟨v,hv⟩ ⟨u,hu⟩ ha
      simp only [Finset.coe_sort_coe,Fintype.card_coe] at hb
      exact ⟨(by positivity : 0≤β/(5*S.card)).trans hb.1,hb.2⟩
    · rw [hzero ⟨v,hv⟩ ⟨u,hu⟩ ha]
      exact ⟨le_refl _,by positivity⟩
  · intro v hv
    have hh:=Finset.sum_subtype (F:=inferInstance) (p:=fun u:V=>u∈S)
      S (fun _=>Iff.rfl) (fun u=>weight s(v,u))
    rw [hh]
    calc
      _ = ∑ u:S,w ⟨v,hv⟩ u:=by
        apply Finset.sum_congr rfl
        intro u _
        simp only [he,f,dite_eq_left hv,dite_eq_left u.property]
        rfl
      _ = 1:=hsum ⟨v,hv⟩
  · intro v u ha
    rw [he]
    by_cases hv:v∈S <;> by_cases hu:u∈S
    · simp only [f,dite_eq_left hv,dite_eq_left hu]
      exact hzero ⟨v,hv⟩ ⟨u,hu⟩ ha
    all_goals simp [f,hv,hu]
  · intro v hv u hu ha
    rw [he]
    simp only [f,dite_eq_left hv,dite_eq_left hu]
    simpa only [Finset.coe_sort_coe,Fintype.card_coe] using (hbound ⟨v,hv⟩ ⟨u,hu⟩ ha).1

end Oberwolfach
