module

public import Oberwolfach.SparseForbiddenPaths
public import Oberwolfach.PathCycleSupport
public import Oberwolfach.OrdinaryFactorWheels

@[expose] public section

/-! Complete a prescribed pair of root rim edges and a root spoke to an
actual ordinary wheel in a sparse host. Every internal rim vertex avoids
the realised forbidden set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_wheel_from_common_counts_within (Q F : SimpleGraph V) (H : V→U→Prop)
    (A W Ω : Finset V) (hAΩ : A⊆Ω) (x v w : V) (hvΩ : v∈Ω) (hwΩ : w∈Ω) (u:U) (hvw : v≠w)
    (hxv : Q.Adj x v) (hxw : Q.Adj x w)
    (hFroot : ∀ a∈({x,v,w}:Finset V),∀ b∈({x,v,w}:Finset V),¬F.Adj a b)
    (hHroot : H x u∧H v u∧H w u) (hHA : ∀ a∈A,H a u)
    (r : ℕ) (hr : 4≤r) (L b : ℝ) (hL : 0≤L) (hF : ∀ a,(F.degree a:ℝ)≤L)
    (hcount : ∀ a∈Ω,∀ b'∈Ω,b≤((A∩Q.neighborFinset a∩Q.neighborFinset b').card:ℝ))
    (hbudget : W.card+((r:ℝ)+3)*(L+1)<b) :
    ∃ C : OrdinaryWheel Q F H r,ordinaryWheelHub C=u ∧
      (ordinaryWheelRim C).Adj x v ∧ (ordinaryWheelRim C).Adj x w ∧
      (∀ a∈(ordinaryWheelRim C).support,a∈({x,v,w}:Finset V) ∨ a∈A∧a∉W) := by
  let Z:Finset V:={x,v,w}
  have hz : (Z.card:ℝ)≤3:=by exact_mod_cast (Finset.card_le_three (a:=x) (b:=v) (c:=w))
  have hk : ((r-2:ℕ):ℝ)≤r:=by exact_mod_cast Nat.sub_le r 2
  have hbudget' : W.card+((Z.card:ℝ)+(r-2:ℕ))*(L+1)<b:=by
    have hh:=mul_le_mul_of_nonneg_right (show (Z.card:ℝ)+(r-2:ℕ)≤(r:ℝ)+3 by linarith)
      (show 0≤L+1 by linarith)
    linarith only [hh,hbudget]
  obtain ⟨p,hp,hlen,hclass,hind,hroot⟩:=sparse_fixed_length_forbidden_path_within Q F A W Z Ω hAΩ v w hvΩ hwΩ hvw
    (by simp [Z]) (by simp [Z]) hFroot (r-2) (by omega) L b hL hF hcount hbudget'
  have hxp : x∉p.support:=by
    intro hx
    rcases hclass x hx with he|he|hc
    · exact hxv.ne he
    · exact hxw.ne he
    · exact hc.2.2 (by simp [Z])
  let q : Q.Walk x w:=p.cons hxv
  have hq : q.IsPath:=by
    exact SimpleGraph.Walk.IsPath.cons hp hxp
  have hqlen : q.length=r-1:=by simp only [q,SimpleGraph.Walk.length_cons,hlen];omega
  obtain ⟨C,hC,hCQ,hCxw,hCs,hsteps⟩:=embedded_cycle_from_path_with_support Q r (by omega) x w q hq hqlen hxw
  have hCxv : C.Adj x v:=by
    have hh:=hsteps 0 (by rw [hqlen];omega)
    simpa [q] using hh
  have hHs (a:V) (ha:a∈C.support) : H a u:=by
    have hh:= (hCs a).mp ha
    change a∈(p.cons hxv).support at hh
    rw [SimpleGraph.Walk.support_cons] at hh
    rcases List.mem_cons.mp hh with he|hp'
    · rw [he];exact hHroot.1
    · rcases hclass a hp' with he|he|hc
      · rw [he];exact hHroot.2.1
      · rw [he];exact hHroot.2.2
      · exact hHA a hc.1
  have hFs : ∀ a∈C.support,∀ b∈C.support,¬F.Adj a b:=by
    intro a ha b hb
    have ha':=(hCs a).mp ha
    have hb':=(hCs b).mp hb
    change a∈(p.cons hxv).support at ha'
    change b∈(p.cons hxv).support at hb'
    simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at ha' hb'
    rcases ha' with he|ha' <;> rcases hb' with he'|hb'
    · rw [he,he'];exact F.loopless.irrefl x
    · rw [he];exact fun h=>hroot b hb' x (by simp [Z]) h.symm
    · rw [he'];exact hroot a ha' x (by simp [Z])
    · exact hind a ha' b hb'
  let wheel : OrdinaryWheel Q F H r:=⟨(⟨⟨C,hC⟩,hCQ⟩,u),hHs,hFs⟩
  refine ⟨wheel,rfl,hCxv,hCxw,?_⟩
  intro a ha
  have hh:=(hCs a).mp ha
  change a∈(p.cons hxv).support at hh
  simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hh
  rcases hh with he|hp'
  · exact Or.inl (by simp [he])
  · rcases hclass a hp' with he|he|hc
    · exact Or.inl (by simp [he])
    · exact Or.inl (by simp [he])
    · exact Or.inr ⟨hc.1,hc.2.1⟩


theorem ordinary_root_wheel_from_common_counts (Q F : SimpleGraph V) (H : V→U→Prop)
    (A W : Finset V) (x v w : V) (u:U) (hvw : v≠w)
    (hxv : Q.Adj x v) (hxw : Q.Adj x w)
    (hFroot : ∀ a∈({x,v,w}:Finset V),∀ b∈({x,v,w}:Finset V),¬F.Adj a b)
    (hHroot : H x u∧H v u∧H w u) (hHA : ∀ a∈A,H a u)
    (r : ℕ) (hr : 4≤r) (L b : ℝ) (hL : 0≤L) (hF : ∀ a,(F.degree a:ℝ)≤L)
    (hcount : ∀ a b',b≤((A∩Q.neighborFinset a∩Q.neighborFinset b').card:ℝ))
    (hbudget : W.card+((r:ℝ)+3)*(L+1)<b) :
    ∃ C : OrdinaryWheel Q F H r,ordinaryWheelHub C=u ∧
      (ordinaryWheelRim C).Adj x v ∧ (ordinaryWheelRim C).Adj x w ∧
      (∀ a∈(ordinaryWheelRim C).support,a∈({x,v,w}:Finset V) ∨ a∈A∧a∉W) := by
  exact ordinary_root_wheel_from_common_counts_within Q F H A W Finset.univ (Finset.subset_univ _)
    x v w (Finset.mem_univ _) (Finset.mem_univ _) u hvw hxv hxw hFroot hHroot hHA
    r hr L b hL hF (fun a _ b' _=>hcount a b') hbudget

end Oberwolfach
