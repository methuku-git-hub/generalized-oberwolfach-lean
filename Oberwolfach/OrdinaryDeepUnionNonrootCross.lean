module

public import Oberwolfach.OrdinaryDeepUnionNonrootDegree

@[expose] public section
/-! The second root-cover packing avoids inner nonroots. Consequently every
edge from an outside vertex to those nonroots comes from the low-load first
packing, with no charge proportional to the number of roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_deep_union_nonroot_cross
    (R RE RM:SimpleGraph V) (S SE SM:V→U→Prop) (I T:Finset V) (J W:Finset U) (L:ℝ)
    (hL:0≤L) (hR:R=RE⊔RM) (hS:∀v u,S v u↔SE v u∨SM v u)
    (hAvoidR:∀v∈I\T,∀w,¬RM.Adj v w)
    (hAvoidC:∀u∈J\W,∀v,¬SM v u)
    (hRcost:∀v,(RE.degree v:ℝ)≤2*L)
    (hScost:∀v,((Finset.univ.filter (SE v)).card:ℝ)≤L):
    ∀v,|((R.neighborFinset v∩(I\T)).card:ℝ)-2*((J\W).filter (S v)).card|≤2*L:=by
  intro v
  have hrim:R.neighborFinset v∩(I\T)⊆RE.neighborFinset v:=by
    intro w hw
    have hvw:R.Adj v w:=(R.mem_neighborFinset v w).mp (Finset.mem_inter.mp hw).1
    have hwI:w∈I\T:=(Finset.mem_inter.mp hw).2
    rw [hR,SimpleGraph.sup_adj] at hvw
    rcases hvw with h|h
    · exact (RE.mem_neighborFinset v w).mpr h
    · exact ((hAvoidR w hwI v) h.symm).elim
  have hsp:(J\W).filter (S v)⊆Finset.univ.filter (SE v):=by
    intro u hu
    have huJ:u∈J\W:=(Finset.mem_filter.mp hu).1
    have hvu:S v u:=(Finset.mem_filter.mp hu).2
    rcases (hS v u).mp hvu with h|h
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
    · exact ((hAvoidC u huJ v) h).elim
  have ha:(((R.neighborFinset v∩(I\T)).card):ℝ)≤2*L:=by
    have hh:=Finset.card_le_card hrim
    rw [SimpleGraph.card_neighborFinset_eq_degree] at hh
    have hr:(((R.neighborFinset v∩(I\T)).card):ℝ)≤RE.degree v:=by exact_mod_cast hh
    exact hr.trans (hRcost v)
  have hb:((((J\W).filter (S v)).card):ℝ)≤L:=by
    have hh:=Finset.card_le_card hsp
    have hs:((((J\W).filter (S v)).card):ℝ)≤(Finset.univ.filter (SE v)).card:=by exact_mod_cast hh
    exact hs.trans (hScost v)
  have ha0:0≤(((R.neighborFinset v∩(I\T)).card):ℝ):=by positivity
  have hb0:0≤((((J\W).filter (S v)).card):ℝ):=by positivity
  apply abs_le.mpr
  constructor <;> linarith only [ha,hb,ha0,hb0,hL]
end Oberwolfach
