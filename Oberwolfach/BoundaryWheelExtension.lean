module

public import Oberwolfach.SparsePathDeletion
public import Oberwolfach.OrdinaryWheelFamilies

@[expose] public section

/-! Complete the two assigned boundary rim edges using only inner
vertices. Used or reserved spokes are removed from the hub's candidate
set. Only deletion degrees at inner vertices are required. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem boundary_wheel_after_deletion (Q D F:SimpleGraph V) (H E:V→U→Prop)
    (A W Ω:Finset V) (hAΩ:A⊆Ω) (x v w:V) (u:U) (hvΩ:v∈Ω) (hwΩ:w∈Ω)
    (hvw:v≠w) (hxv:Q.Adj x v) (hxw:Q.Adj x w)
    (hDxv:¬D.Adj x v) (hDxw:¬D.Adj x w)
    (hFroot:∀ a∈({x,v,w}:Finset V),∀ b∈({x,v,w}:Finset V),¬F.Adj a b)
    (hHroot:H x u∧H v u∧H w u) (hEroot:¬E x u∧¬E v u∧¬E w u)
    (hHA:∀ a∈A,H a u) (r:ℕ) (hr:4≤r) (L d e b:ℝ) (hL:0≤L)
    (hF:∀ a,(F.degree a:ℝ)≤L) (hD:∀ a∈Ω,(D.degree a:ℝ)≤d)
    (hE:((Finset.univ.filter (fun a=>E a u)).card:ℝ)≤e)
    (hcount:∀ a∈Ω,∀ c∈Ω,b≤((A∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ))
    (hbudget:W.card+((r:ℝ)+3)*(L+1)+2*d+e<b):
    ∃ C:OrdinaryWheel Q F H r,ordinaryWheelHub C=u ∧
      (ordinaryWheelRim C).Adj x v ∧ (ordinaryWheelRim C).Adj x w ∧
      Disjoint (ordinaryWheelResources C) (ordinaryHostResources D E) ∧
      (∀ a∈(ordinaryWheelRim C).support,a∈({x,v,w}:Finset V) ∨ a∈A∧a∉W):=by
  let Z:=Finset.univ.filter (fun a=>E a u)
  let A₀:=A\Z
  have hcounts (a:V) (ha:a∈Ω) (c:V) (hc:c∈Ω):
      b-2*d-e≤((A₀∩(Q\D).neighborFinset a∩(Q\D).neighborFinset c).card:ℝ):=by
    have hdel:=two_common_neighbours_after_deletion Q D A a c
    have hrem:=Finset.card_le_card_sdiff_add_card
      (s:=A∩(Q\D).neighborFinset a∩(Q\D).neighborFinset c) (t:=Z)
    have he:(A∩(Q\D).neighborFinset a∩(Q\D).neighborFinset c)\Z=
        A₀∩(Q\D).neighborFinset a∩(Q\D).neighborFinset c:=by
      ext z;simp only [A₀,Finset.mem_sdiff,Finset.mem_inter];tauto
    rw [he] at hrem
    have hd':((A∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ)≤
      (A∩(Q\D).neighborFinset a∩(Q\D).neighborFinset c).card+D.degree a+D.degree c:=by exact_mod_cast hdel
    have hr':((A∩(Q\D).neighborFinset a∩(Q\D).neighborFinset c).card:ℝ)≤
      (A₀∩(Q\D).neighborFinset a∩(Q\D).neighborFinset c).card+Z.card:=by exact_mod_cast hrem
    linarith only [hd',hr',hD a ha,hD c hc,hE,hcount a ha c hc]
  obtain ⟨C,hCu,hCv,hCw,hCs⟩:=ordinary_root_wheel_from_common_counts_within (Q\D) F H
    A₀ W Ω (Finset.sdiff_subset.trans hAΩ) x v w hvΩ hwΩ u hvw
    ⟨hxv,hDxv⟩ ⟨hxw,hDxw⟩ hFroot hHroot (fun a ha=>hHA a (Finset.mem_sdiff.mp ha).1)
    r hr L (b-2*d-e) hL hF
    (by intro a ha c hc;convert hcounts a ha c hc using 1;congr 2;ext z;simp only [Finset.mem_inter,SimpleGraph.mem_neighborFinset])
    (by linarith only [hbudget])
  let C':OrdinaryWheel Q F H r:=ordinaryWheelInclude sdiff_le C
  have hspoke (a:V) (ha:a∈(ordinaryWheelRim C').support):¬E a u:=by
    rcases hCs a ha with hroot|hfree
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hroot
      rcases hroot with rfl|rfl|rfl
      · exact hEroot.1
      · exact hEroot.2.1
      · exact hEroot.2.2
    · have hn: a∉Z:=(Finset.mem_sdiff.mp hfree.1).2
      simpa only [Z,Finset.mem_filter,Finset.mem_univ,true_and] using hn
  refine ⟨C',hCu,hCv,hCw,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro z hz hzD
    cases z with
    | inl edge=>
      rw [ordinaryWheelResources_rim] at hz
      rw [ordinaryHostResources_rim] at hzD
      induction edge using Sym2.ind with
      | _ a c=>exact ((C.val.1.property hz).2 hzD)
    | inr au=>
      rcases au with ⟨a,u'⟩
      rw [ordinaryWheelResources_spoke] at hz
      rw [ordinaryHostResources_spoke] at hzD
      have he:u'=u:=hz.1.symm.trans hCu
      exact hspoke a hz.2 (he ▸ hzD)
  · intro a ha
    rcases hCs a ha with hroot|hfree
    · exact Or.inl hroot
    · exact Or.inr ⟨(Finset.mem_sdiff.mp hfree.1).1,hfree.2⟩

end Oberwolfach
