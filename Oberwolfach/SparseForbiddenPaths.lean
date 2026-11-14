module

public import Oberwolfach.SparsePathChoices

@[expose] public section

/-! Fixed-length paths in a sparse host with external roots, forbidden
vertices and forbidden vertex pairs. The hypotheses are common-neighbour
counts, not a dense minimum-degree assumption on the sparse graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem sparse_path_prefix_within (Q F : SimpleGraph V) (A W Z Ω : Finset V) (hAΩ : A⊆Ω) (x : V) (hxΩ : x∈Ω) (hx : x∈Z)
    (hZ : ∀ v∈Z,∀ w∈Z,¬F.Adj v w) (k : ℕ) (L b : ℝ)
    (hL : 0≤L) (hF : ∀ v,(F.degree v:ℝ)≤L)
    (hcount : ∀ v∈Ω,b≤((A∩Q.neighborFinset v∩Q.neighborFinset v).card:ℝ))
    (hbudget : W.card+((Z.card:ℝ)+k+1)*(L+1)<b) :
    ∃ z,∃ p : Q.Walk x z,p.IsPath ∧ p.length=k ∧
      (∀ v∈p.support,v=x ∨ v∈A ∧ v∉W ∧ v∉Z) ∧
      (∀ v∈p.support,∀ w∈p.support,¬F.Adj v w) ∧
      (∀ v∈p.support,∀ w∈Z,¬F.Adj v w) := by
  induction k with
  | zero =>
    refine ⟨x,SimpleGraph.Walk.nil,by simp,by simp,?_,?_,?_⟩
    · intro v hv
      have hvx : v=x:=by simpa using hv
      exact Or.inl hvx
    · intro v hv w hw
      have hvx : v=x:=by simpa using hv
      have hwx : w=x:=by simpa using hw
      rw [hvx,hwx]
      exact F.loopless.irrefl x
    · intro v hv w hw
      have hvx : v=x:=by simpa using hv
      rw [hvx]
      exact hZ x hx w hw
  | succ k ih =>
    have hsmall : W.card+((Z.card:ℝ)+k+1)*(L+1)<b:=by
      push_cast at hbudget
      nlinarith only [hbudget,hL]
    obtain ⟨z,p,hp,hlen,hclass,hind,hroot⟩:=ih hsmall
    have hsupport : p.support.toFinset.card≤k+1:=by
      exact (List.toFinset_card_le _).trans_eq (by rw [p.length_support,hlen])
    have hused : ((Z∪p.support.toFinset).card:ℝ)≤Z.card+k+1:=by
      have hh:=(Finset.card_union_le Z p.support.toFinset).trans (Nat.add_le_add_left hsupport Z.card)
      exact_mod_cast hh
    have hb' : W.card+((Z∪p.support.toFinset).card:ℝ)*(L+1)<b:=by
      have hh:=mul_le_mul_of_nonneg_right hused (show 0≤L+1 by linarith)
      linarith only [hh,hsmall]
    obtain ⟨v,hvA,hvW,hvZ,hzv,_,hFv⟩:=sparse_common_neighbour_avoiding Q F A W
      (Z∪p.support.toFinset) z z L b hL hF (hcount z (by
        rcases hclass z p.end_mem_support with he|hz
        · exact he ▸ hxΩ
        · exact hAΩ hz.1)) hb'
    have hvp : v∉p.support:=fun h=>hvZ (Finset.mem_union_right _ (List.mem_toFinset.mpr h))
    have hvZ' : v∉Z:=fun h=>hvZ (Finset.mem_union_left _ h)
    refine ⟨v,p.concat hzv,hp.concat hvp hzv,by simp [hlen],?_,?_,?_⟩
    · intro w hw
      rw [SimpleGraph.Walk.support_concat] at hw
      rcases List.mem_append.mp hw with hw|hw
      · exact hclass w hw
      · have hwv:=List.mem_singleton.mp hw;subst w;exact Or.inr ⟨hvA,hvW,hvZ'⟩
    · intro w hw z' hz'
      simp only [SimpleGraph.Walk.support_concat,List.mem_append,List.mem_singleton] at hw hz'
      rcases hw with hw|he <;> rcases hz' with hz'|he'
      · exact hind w hw z' hz'
      · rw [he'];exact fun he=>hFv w (Finset.mem_union_right _ (List.mem_toFinset.mpr hw)) he.symm
      · rw [he];exact hFv z' (Finset.mem_union_right _ (List.mem_toFinset.mpr hz'))
      · rw [he,he'];exact F.loopless.irrefl v
    · intro w hw z' hz'
      simp only [SimpleGraph.Walk.support_concat,List.mem_append,List.mem_singleton] at hw
      rcases hw with hw|rfl
      · exact hroot w hw z' hz'
      · exact hFv z' (Finset.mem_union_left _ hz')

theorem sparse_fixed_length_forbidden_path_within (Q F : SimpleGraph V) (A W Z Ω : Finset V) (hAΩ : A⊆Ω)
    (x y : V) (hxΩ : x∈Ω) (hyΩ : y∈Ω) (hxy : x≠y) (hx : x∈Z) (hy : y∈Z)
    (hZ : ∀ v∈Z,∀ w∈Z,¬F.Adj v w) (k : ℕ) (hk : 2≤k) (L b : ℝ)
    (hL : 0≤L) (hF : ∀ v,(F.degree v:ℝ)≤L)
    (hcount : ∀ v∈Ω,∀ w∈Ω,b≤((A∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hbudget : W.card+((Z.card:ℝ)+k)*(L+1)<b) :
    ∃ p : Q.Walk x y,p.IsPath ∧ p.length=k ∧
      (∀ v∈p.support,v=x ∨ v=y ∨ v∈A ∧ v∉W ∧ v∉Z) ∧
      (∀ v∈p.support,∀ w∈p.support,¬F.Adj v w) ∧
      (∀ v∈p.support,∀ w∈Z,¬F.Adj v w) := by
  have hkR : ((k-2:ℕ):ℝ)+2=k:=by exact_mod_cast (show k-2+2=k by omega)
  obtain ⟨z,p,hp,hlen,hclass,hind,hroot⟩:=sparse_path_prefix_within Q F A W Z Ω hAΩ x hxΩ hx hZ (k-2) L b hL hF
    (fun v hv=>hcount v hv v hv) (by nlinarith only [hbudget,hkR,hL])
  have hsupport : p.support.toFinset.card≤k-1:=by
    have hh:=List.toFinset_card_le p.support
    rw [p.length_support,hlen] at hh
    omega
  have hused : ((Z∪p.support.toFinset).card:ℝ)≤Z.card+k:=by
    have hh:=(Finset.card_union_le Z p.support.toFinset).trans (Nat.add_le_add_left (hsupport.trans (show k-1≤k by omega)) Z.card)
    exact_mod_cast hh
  have hb' : W.card+((Z∪p.support.toFinset).card:ℝ)*(L+1)<b:=by
    have hh:=mul_le_mul_of_nonneg_right hused (show 0≤L+1 by linarith)
    linarith only [hh,hbudget]
  obtain ⟨v,hvA,hvW,hvZ,hzv,hyv,hFv⟩:=sparse_common_neighbour_avoiding Q F A W
    (Z∪p.support.toFinset) z y L b hL hF (hcount z (by
      rcases hclass z p.end_mem_support with he|hz
      · exact he ▸ hxΩ
      · exact hAΩ hz.1) y hyΩ) hb'
  have hvp : v∉p.support:=fun h=>hvZ (Finset.mem_union_right _ (List.mem_toFinset.mpr h))
  have hvZ' : v∉Z:=fun h=>hvZ (Finset.mem_union_left _ h)
  have hyp : y∉p.support:=by
    intro h
    rcases hclass y h with he|hrest
    · exact hxy he.symm
    · exact hrest.2.2 hy
  have hyp' : y∉(p.concat hzv).support:=by
    simp only [SimpleGraph.Walk.support_concat,List.mem_append,List.mem_singleton,not_or]
    exact ⟨hyp,fun he=>hvZ' (he ▸ hy)⟩
  have hlist (w:V) : w∈((p.concat hzv).concat hyv.symm).support ↔ w∈p.support ∨ w=v ∨ w=y:=by
    simp only [SimpleGraph.Walk.support_concat,List.mem_append,List.mem_singleton,or_assoc]
  have hind' : ∀ w∈p.support,¬F.Adj w v:=fun w hw he=>hFv w (Finset.mem_union_right _ (List.mem_toFinset.mpr hw)) he.symm
  have hvin : ∀ w∈Z,¬F.Adj v w:=fun w hw=>hFv w (Finset.mem_union_left _ hw)
  refine ⟨(p.concat hzv).concat hyv.symm,(hp.concat hvp hzv).concat hyp' hyv.symm,?_,?_,?_,?_⟩
  · simp only [SimpleGraph.Walk.length_concat,hlen];omega
  · intro w hw
    rcases (hlist w).mp hw with hw|rfl|rfl
    · rcases hclass w hw with he|hc
      · exact Or.inl he
      · exact Or.inr (Or.inr hc)
    · exact Or.inr (Or.inr ⟨hvA,hvW,hvZ'⟩)
    · exact Or.inr (Or.inl rfl)
  · intro w hw t ht
    rcases (hlist w).mp hw with hw'|he|he <;> rcases (hlist t).mp ht with ht'|he'|he'
    · exact hind w hw' t ht'
    · rw [he'];exact hind' w hw'
    · rw [he'];exact hroot w hw' y hy
    · rw [he];exact fun h=>hind' t ht' h.symm
    · rw [he,he'];exact F.loopless.irrefl v
    · rw [he,he'];exact hvin y hy
    · rw [he];exact fun h=>hroot t ht' y hy h.symm
    · rw [he,he'];exact fun h=>hvin y hy h.symm
    · rw [he,he'];exact F.loopless.irrefl y
  · intro w hw t ht
    rcases (hlist w).mp hw with hw'|he|he
    · exact hroot w hw' t ht
    · rw [he];exact hvin t ht
    · rw [he];exact hZ y hy t ht


theorem sparse_fixed_length_forbidden_path (Q F : SimpleGraph V) (A W Z : Finset V)
    (x y : V) (hxy : x≠y) (hx : x∈Z) (hy : y∈Z)
    (hZ : ∀ v∈Z,∀ w∈Z,¬F.Adj v w) (k : ℕ) (hk : 2≤k) (L b : ℝ)
    (hL : 0≤L) (hF : ∀ v,(F.degree v:ℝ)≤L)
    (hcount : ∀ v w,b≤((A∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hbudget : W.card+((Z.card:ℝ)+k)*(L+1)<b) :
    ∃ p : Q.Walk x y,p.IsPath ∧ p.length=k ∧
      (∀ v∈p.support,v=x ∨ v=y ∨ v∈A ∧ v∉W ∧ v∉Z) ∧
      (∀ v∈p.support,∀ w∈p.support,¬F.Adj v w) ∧
      (∀ v∈p.support,∀ w∈Z,¬F.Adj v w) := by
  exact sparse_fixed_length_forbidden_path_within Q F A W Z Finset.univ (Finset.subset_univ _)
    x y (Finset.mem_univ _) (Finset.mem_univ _) hxy hx hy hZ k hk L b hL hF
    (fun v _ w _=>hcount v w) hbudget

end Oberwolfach
