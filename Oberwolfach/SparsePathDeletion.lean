module

public import Oberwolfach.SparseRootWheels
public import Oberwolfach.OrdinaryWheelHostInclusion

@[expose] public section

/-! Local deletion bounds require degrees only at the queried endpoints.
In particular they do not assume a small deletion degree at the row root
whose incident edges are being covered. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem two_common_neighbours_after_deletion (Q D : SimpleGraph V) (A : Finset V)
    (x y : V) :
    (A∩Q.neighborFinset x∩Q.neighborFinset y).card≤
      (A∩(Q\D).neighborFinset x∩(Q\D).neighborFinset y).card+D.degree x+D.degree y := by
  let C:=A∩(Q\D).neighborFinset x∩(Q\D).neighborFinset y
  have hs : A∩Q.neighborFinset x∩Q.neighborFinset y⊆C∪(D.neighborFinset x∪D.neighborFinset y):=by
    intro v hv
    have hvA:=(Finset.mem_inter.mp (Finset.mem_inter.mp hv).1).1
    have hx:=(Q.mem_neighborFinset x v).mp (Finset.mem_inter.mp (Finset.mem_inter.mp hv).1).2
    have hy:=(Q.mem_neighborFinset y v).mp (Finset.mem_inter.mp hv).2
    by_cases hDx:D.Adj x v
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ ((D.mem_neighborFinset x v).mpr hDx))
    by_cases hDy:D.Adj y v
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ ((D.mem_neighborFinset y v).mpr hDy))
    exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr
      ⟨hvA,((Q\D).mem_neighborFinset x v).mpr ⟨hx,hDx⟩⟩,((Q\D).mem_neighborFinset y v).mpr ⟨hy,hDy⟩⟩)
  have hh:=(Finset.card_le_card hs).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (Finset.card_union_le _ _) C.card))
  simpa only [SimpleGraph.card_neighborFinset_eq_degree,Nat.add_assoc] using hh

theorem ordinary_root_wheel_after_local_deletion (Q D F : SimpleGraph V) (H : V→U→Prop)
    (A W : Finset V) (x v w : V) (u:U) (hxA:x∉A) (hvw:v≠w)
    (hxv:Q.Adj x v) (hxw:Q.Adj x w) (hDxv:¬D.Adj x v) (hDxw:¬D.Adj x w)
    (hFroot:∀ a∈({x,v,w}:Finset V),∀ b∈({x,v,w}:Finset V),¬F.Adj a b)
    (hHroot:H x u∧H v u∧H w u) (hHA:∀ a∈A,H a u)
    (r:ℕ) (hr:4≤r) (L d b:ℝ) (hL:0≤L)
    (hF:∀ a,(F.degree a:ℝ)≤L) (hD:∀ a,a≠x → (D.degree a:ℝ)≤d)
    (hcount:∀ a,a≠x → ∀ b',b'≠x → b≤((A∩Q.neighborFinset a∩Q.neighborFinset b').card:ℝ))
    (hbudget:W.card+((r:ℝ)+3)*(L+1)+2*d<b) :
    ∃ C:OrdinaryWheel Q F H r,ordinaryWheelHub C=u ∧
      (ordinaryWheelRim C).Adj x v ∧ (ordinaryWheelRim C).Adj x w ∧
      Disjoint (ordinaryWheelRim C) D ∧
      (∀ a∈(ordinaryWheelRim C).support,a∈({x,v,w}:Finset V) ∨ a∈A∧a∉W) := by
  let Ω:Finset V:=Finset.univ\{x}
  have hAΩ:A⊆Ω:=by
    intro a ha
    simp only [Ω,Finset.mem_sdiff,Finset.mem_univ,Finset.mem_singleton,true_and]
    intro he
    exact hxA (he ▸ ha)
  have hcounts (a:V) (ha:a∈Ω) (b':V) (hb':b'∈Ω) :
      b-2*d≤((A∩(Q\D).neighborFinset a∩(Q\D).neighborFinset b').card:ℝ):=by
    have hax:a≠x:=by simpa only [Ω,Finset.mem_sdiff,Finset.mem_univ,Finset.mem_singleton,true_and] using ha
    have hbx:b'≠x:=by simpa only [Ω,Finset.mem_sdiff,Finset.mem_univ,Finset.mem_singleton,true_and] using hb'
    have hh:=two_common_neighbours_after_deletion Q D A a b'
    have hhR : ((A∩Q.neighborFinset a∩Q.neighborFinset b').card:ℝ)≤
      (A∩(Q\D).neighborFinset a∩(Q\D).neighborFinset b').card+D.degree a+D.degree b':=by exact_mod_cast hh
    linarith only [hhR,hcount a hax b' hbx,hD a hax,hD b' hbx]
  obtain ⟨C,hCu,hCxv,hCxw,hCs⟩:=ordinary_root_wheel_from_common_counts_within (Q\D) F H A W Ω hAΩ x v w
    (by simp [Ω,hxv.ne.symm]) (by simp [Ω,hxw.ne.symm]) u hvw ⟨hxv,hDxv⟩ ⟨hxw,hDxw⟩ hFroot hHroot hHA
    r hr L (b-2*d) hL hF (by intro a ha b' hb';convert hcounts a ha b' hb' using 1 <;> congr!) (by linarith only [hbudget])
  refine ⟨ordinaryWheelInclude sdiff_le C,hCu,hCxv,hCxw,?_,hCs⟩
  apply disjoint_iff_inf_le.mpr
  intro a b' he
  exact ((C.val.1.property he.1).2 he.2).elim

end Oberwolfach
