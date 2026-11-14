module

public import Oberwolfach.MarkedTransformerPathWheels
public import Oberwolfach.MarkedTwoRootPathWheels
public import Oberwolfach.MarkedBoundaryExtensionCounts

@[expose] public section

/-! Complete a prescribed rim arc at a fixed compatible hub, using only
inner free labels. All local counts remain on their original inner domain.
The unique marked arc and its marked spoke agree after canonical rotation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [DecidableEq V]

theorem marked_rim_wheel_on_inner_domain
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop)
    (π:Equiv.Perm V) (b l:ℕ) (hl:2≤l) (X W:Finset V) (v w:V) (u:U) (j:Bool) (c:ℝ)
    (hvw:¬PermutationClose π b v w)
    (hroot:markedArcPresent tail head ktail khead j v w)
    (hv:H₀ v u) (hw:if j then HK w u else H₀ w u)
    (hstep:∀ t x,c≤((X.filter (fun z=>markedArcPresent tail head ktail khead t x z∧
      (if t then HK z u else H₀ z u))).card:ℝ))
    (hjoin:∀ t x y,x≠(if t then π y else y)→c≤((X.filter (fun z=>
      markedArcPresent tail head ktail khead false x z∧
      markedArcPresent tail head ktail khead t z y∧H₀ z u)).card:ℝ))
    (hbudget:(W.card:ℝ)+(l+6)*(2*b+1)<c):
    ∃ p:Fin (l+3)↪V,∃ A:MarkedWheel tail head ktail khead (l+4) π b H₀ HK,
      A.2.val=u∧(∀ i,A.1.val i=Fin.cons (α:=fun _=>V) v (Fin.cons w p) (canonicalMarkedRotation (if j then 0 else 3) i))∧
      (∀ i,p i∈X∧p i∉W∧¬PermutationClose π b (p i) v∧¬PermutationClose π b (p i) w)∧PermutationSeparated π b p:=by
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
  obtain ⟨a,ha⟩:=exists_ne v
  have hclose₀:c≤((X.filter (fun z=>markedArcPresent tail head ktail khead false z v∧H₀ z u)).card:ℝ):=by
    apply (hjoin false a v ha).trans
    exact_mod_cast Finset.card_le_card (show X.filter (fun z=>markedArcPresent tail head ktail khead false a z∧
      markedArcPresent tail head ktail khead false z v∧H₀ z u)⊆X.filter (fun z=>markedArcPresent tail head ktail khead false z v∧H₀ z u) from
      fun z hz=>Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,(Finset.mem_filter.mp hz).2.2⟩)
  have hs (t:Bool) (x:V):c≤((Finset.univ.filter (fun z=>(if t then RK x z else R₀ x z)∧
      (if t then HK' z u∧HK' z u else H₀' z u∧H₀' z u))).card:ℝ):=by
    have he:Finset.univ.filter (fun z=>(if t then RK x z else R₀ x z)∧
        (if t then HK' z u∧HK' z u else H₀' z u∧H₀' z u))=
        X.filter (fun z=>markedArcPresent tail head ktail khead t x z∧(if t then HK z u else H₀ z u)):=by
      ext z;cases t <;> simp [R₀,RK,H₀',HK',markedArcPresent,and_comm,and_left_comm,and_assoc]
    rw [he];exact hstep t x
  have ho:c≤((Finset.univ.filter (fun z=>R₀ w z∧R₀ w z∧H₀' z u∧H₀' z u)).card:ℝ):=by
    simpa only [Bool.false_eq_true,ite_false,and_self,and_self_left] using hs false w
  have hc:c≤((Finset.univ.filter (fun z=>(R₀ z v∧R₀ z v)∧H₀' z u∧H₀' z u)).card:ℝ):=by
    have he:Finset.univ.filter (fun z=>(R₀ z v∧R₀ z v)∧H₀' z u∧H₀' z u)=
        X.filter (fun z=>markedArcPresent tail head ktail khead false z v∧H₀ z u):=by
      ext z;simp [R₀,H₀',markedArcPresent,and_comm,and_left_comm,and_assoc]
    rw [he];exact hclose₀
  have hj:∀ x y,x≠y→c≤((Finset.univ.filter (fun z=>R₀ x z∧R₀ z y∧H₀' z u∧H₀' z u)).card:ℝ):=by
    intro x y hxy
    have he:Finset.univ.filter (fun z=>R₀ x z∧R₀ z y∧H₀' z u∧H₀' z u)=
      X.filter (fun z=>markedArcPresent tail head ktail khead false x z∧markedArcPresent tail head ktail khead false z y∧H₀ z u):=by
      ext z;simp [R₀,H₀',markedArcPresent,and_comm,and_left_comm,and_assoc]
    rw [he];exact hjoin false x y hxy
  let F:=permutationConflictGraph π b
  have hF:∀ x,(F.degree x:ℝ)≤2*b:=by intro x;exact_mod_cast permutationConflictGraph_degree_le π b x
  obtain ⟨p,hop,hcl,hpa,hsp,havoid,hsep⟩:=marked_transformer_between_roots_path F R₀ RK H₀' HK' w w v v u u j false W {v,w}
    l hl (2*b) c (by positivity) hF
    (by convert ho using 1 <;> congr!) (by simp only [Bool.false_eq_true,ite_false];convert hc using 1 <;> congr!)
    (by intro t x;convert hs t x using 1 <;> congr!)
    (by intro x y hxy;convert hj x y hxy using 1 <;> congr!)
    (by
      have hz:(({v,w}:Finset V).card:ℝ)≤2:=by exact_mod_cast Finset.card_le_two
      have hb:0≤(2*b+1:ℝ):=by positivity
      nlinarith only [hbudget,mul_le_mul_of_nonneg_right hz hb])
  have hfree:PermutationSeparated π b p:=by
    intro i k hik hh;exact hsep i k ⟨fun h=>hik (p.injective h),hh⟩
  have hout (i:Fin (l+3)) (z:V) (hz:z∈({v,w}:Finset V)):¬PermutationClose π b (p i) z:=by
    intro h;exact (havoid i).2.2 z hz ⟨fun he=>(havoid i).2.1 (he ▸ hz),h⟩
  have hcons:PermutationSeparated π b (Fin.cons v (Fin.cons w p)):=by
    apply permutationSeparated_cons
    · exact permutationSeparated_cons π b w p hfree
        (fun i h=>hout i w (by simp) ((permutationClose_symm π b w (p i)).mp h))
    · intro i
      refine Fin.cases ?_ (fun i=>?_) i
      · exact hvw
      · intro h;exact hout i v (by simp) ((permutationClose_symm π b v (p i)).mp h)
  have hcl₀:∃ e,tail e=p (Fin.last (l+2))∧head e=v:=hcl.1
  have hsp₀:∀ i,if j=false∧i.val=2 then HK (p i) u else H₀ (p i) u:=by
    intro i;have h:=hsp i;split_ifs at h ⊢ <;> exact h.1.1
  have hpX:∀ i,p i∈X:=by
    intro i;have h:=hsp i;split_ifs at h <;> exact h.1.2
  obtain ⟨A,hAu,hA⟩:=marked_wheel_from_two_root_path tail head ktail khead (l+2) (by omega)
    π b H₀ HK j v w u p hcons hroot hop.1 hcl₀ hpa hv hw hsp₀
  exact ⟨p,A,hAu,hA,fun i=>⟨hpX i,(havoid i).1,hout i v (by simp),hout i w (by simp)⟩,hfree⟩
end Oberwolfach
