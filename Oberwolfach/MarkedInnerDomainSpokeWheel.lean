module

public import Oberwolfach.MarkedTransformerPathWheels
public import Oberwolfach.MarkedBoundaryExtensionCounts

@[expose] public section

/-! A prescribed spoke is completed using free labels in the inner set.
The candidate counts are measured on that set; its complement is never
charged as a forbidden set. The marked head and root spoke retain their types. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [DecidableEq V]

theorem marked_spoke_wheel_on_inner_domain
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop)
    (π:Equiv.Perm V) (b l:ℕ) (hl:2≤l) (X W:Finset V) (v:V) (u:U) (j:Bool) (c:ℝ)
    (hroot:if j then HK v u else H₀ v u)
    (hstep:∀ t x,c≤((X.filter (fun z=>markedArcPresent tail head ktail khead t x z∧
      (if t then HK z u else H₀ z u))).card:ℝ))
    (hjoin:∀ t x y,x≠(if t then π y else y)→c≤((X.filter (fun z=>
      markedArcPresent tail head ktail khead false x z∧
      markedArcPresent tail head ktail khead t z y∧H₀ z u)).card:ℝ))
    (hbudget:(W.card:ℝ)+(l+5)*(2*b+1)<c):
    ∃ p:Fin (l+3)↪V,∃ A:MarkedWheel tail head ktail khead (l+3) π b H₀ HK,
      A.2.val=u∧(∀ i,A.1.val i=rootedCycleOrder (markedRootOrder (l+3) j) v p i)∧
      (∀ i,p i∈X∧p i∉W∧¬PermutationClose π b (p i) v)∧PermutationSeparated π b p:=by
  let R₀:=fun x y=>∃ e,tail e=x∧head e=y
  let RK:=fun x y=>∃ e,ktail e=x∧khead e=y
  let H₀':=fun x u=>H₀ x u∧x∈X
  let HK':=fun x u=>HK x u∧x∈X
  have hcount:c≤(Fintype.card V:ℝ):=by
    apply (hstep false v).trans
    exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _)).trans (Finset.card_le_univ X)
  have hc1:1<c:=by
    have hW:0≤(W.card:ℝ):=Nat.cast_nonneg _
    have hb:0≤(b:ℝ):=Nat.cast_nonneg _
    have hl':0≤(l:ℝ):=Nat.cast_nonneg _
    nlinarith only [hbudget,hW,hb,hl',mul_nonneg hb hl']
  have hn:1<Fintype.card V:=by exact_mod_cast hc1.trans_le hcount
  letI:Nontrivial V:=Fintype.one_lt_card_iff_nontrivial.mp hn
  obtain ⟨w,hw⟩:=exists_ne (if j then π v else v)
  have hclose₀:c≤((X.filter (fun z=>markedArcPresent tail head ktail khead j z v∧H₀ z u)).card:ℝ):=by
    apply (hjoin j w v hw).trans
    exact_mod_cast Finset.card_le_card (show X.filter (fun z=>markedArcPresent tail head ktail khead false w z∧
      markedArcPresent tail head ktail khead j z v∧H₀ z u)⊆X.filter (fun z=>markedArcPresent tail head ktail khead j z v∧H₀ z u) from
      fun z hz=>Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,(Finset.mem_filter.mp hz).2.2⟩)
  have hs (t:Bool) (x:V):c≤((Finset.univ.filter (fun z=>(if t then RK x z else R₀ x z)∧
      (if t then HK' z u∧HK' z u else H₀' z u∧H₀' z u))).card:ℝ):=by
    have he:Finset.univ.filter (fun z=>(if t then RK x z else R₀ x z)∧
        (if t then HK' z u∧HK' z u else H₀' z u∧H₀' z u))=
        X.filter (fun z=>markedArcPresent tail head ktail khead t x z∧(if t then HK z u else H₀ z u)):=by
      ext z;cases t <;> simp [R₀,RK,H₀',HK',markedArcPresent,and_comm,and_left_comm,and_assoc]
    rw [he];exact hstep t x
  have ho:c≤((Finset.univ.filter (fun z=>R₀ v z∧R₀ v z∧H₀' z u∧H₀' z u)).card:ℝ):=by
    simpa only [Bool.false_eq_true,ite_false,and_self,and_self_left] using hs false v
  have hc:c≤((Finset.univ.filter (fun z=>(if j then RK z v∧RK z v else R₀ z v∧R₀ z v)∧H₀' z u∧H₀' z u)).card:ℝ):=by
    have he:Finset.univ.filter (fun z=>(if j then RK z v∧RK z v else R₀ z v∧R₀ z v)∧H₀' z u∧H₀' z u)=
        X.filter (fun z=>markedArcPresent tail head ktail khead j z v∧H₀ z u):=by
      ext z;cases j <;> simp [R₀,RK,H₀',markedArcPresent,and_comm,and_left_comm,and_assoc]
    rw [he];exact hclose₀
  have hj:∀ x y,x≠y→c≤((Finset.univ.filter (fun z=>R₀ x z∧R₀ z y∧H₀' z u∧H₀' z u)).card:ℝ):=by
    intro x y hxy
    have he:Finset.univ.filter (fun z=>R₀ x z∧R₀ z y∧H₀' z u∧H₀' z u)=
      X.filter (fun z=>markedArcPresent tail head ktail khead false x z∧markedArcPresent tail head ktail khead false z y∧H₀ z u):=by
      ext z;simp [R₀,H₀',markedArcPresent,and_comm,and_left_comm,and_assoc]
    rw [he];exact hjoin false x y hxy
  let F:=permutationConflictGraph π b
  have hF:∀ x,(F.degree x:ℝ)≤2*b:=by intro x;exact_mod_cast permutationConflictGraph_degree_le π b x
  obtain ⟨p,hop,hcl,hpa,hsp,havoid,hsep⟩:=marked_transformer_common_path F R₀ RK H₀' HK' v v u u j W {v}
    (by simp) (by simp) l hl (2*b) c (by positivity) hF
    (by convert ho using 1 <;> congr!) (by convert hc using 1 <;> congr!)
    (by intro t x;convert hs t x using 1 <;> congr!)
    (by intro x y hxy;convert hj x y hxy using 1 <;> congr!)
    (by simp only [Finset.card_singleton,Nat.cast_one];nlinarith only [hbudget])
  have hfree:PermutationSeparated π b p:=by
    intro i k hik hh;exact hsep i k ⟨fun h=>hik (p.injective h),hh⟩
  have hout (i:Fin (l+3)):¬PermutationClose π b (p i) v:=by
    intro h;exact (havoid i).2.2 v (by simp) ⟨fun he=>(havoid i).2.1 (by simp [he]),h⟩
  have hcons:PermutationSeparated π b (Fin.cons v p):=
    permutationSeparated_cons π b v p hfree (fun i h=>hout i ((permutationClose_symm π b v (p i)).mp h))
  have hcl₀:if j then ∃ e,ktail e=p (Fin.last (l+2))∧khead e=v else ∃ e,tail e=p (Fin.last (l+2))∧head e=v:=by
    cases j <;> exact hcl.1
  have hsp₀:∀ i,if j=false∧i.val=2 then HK (p i) u else H₀ (p i) u:=by
    intro i;have h:=hsp i;split_ifs at h ⊢ <;> exact h.1.1
  have hpX:∀ i,p i∈X:=by
    intro i;have h:=hsp i;split_ifs at h <;> exact h.1.2
  obtain ⟨A,hAu,hA⟩:=marked_wheel_from_rooted_path tail head ktail khead (l+2) (by omega)
    π b H₀ HK j v u p hcons hop.1 hcl₀ hpa hroot hsp₀
  exact ⟨p,A,hAu,hA,fun i=>⟨hpX i,(havoid i).1,hout i⟩,hfree⟩
end Oberwolfach
