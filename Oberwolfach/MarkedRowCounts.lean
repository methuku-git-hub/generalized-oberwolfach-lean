module

public import Oberwolfach.MarkedRowResources

@[expose] public section

/-! Exact targets and deviation bounds for actual marked row counts.
The admissible domain is fixed before exposure and retains the original
outer set for its error normalization. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def markedRowEligible (P : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ)
    (a : Bool×Bool×V) (z : V) : Prop :=
  ¬PermutationClose π b a.2.2 z ∧
    Sum.elim (fun xy=>P.Adj xy.1 xy.2) (fun xy=>P.Adj xy.1 (π xy.2)) (markedRowRim a z)

def markedRowDomain (P : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ)
    (A : Finset V) (S T : Finset (Bool×Bool×V)) : Finset V :=
  A.filter (fun z=>(∀ a∈S,markedRowEligible P π b a z) ∧
    Set.InjOn (fun a=>markedPairPhysical π (markedRowRim a z)) S ∧
    (∀ a∈T,Sum.elim (fun xy=>P.Adj xy.1 xy.2) (fun xy=>P.Adj xy.1 (π xy.2)) (markedRowRim a z)))

def rawMarkedRowCount (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ)
    (C : Finset V) (S : Finset (Bool×Bool×V)) (J : Finset (Bool×U))
    (g : Γ) (j : Color) (σ : RawMarkedOutcome V U Γ Color) : ℝ :=
  ∑ z∈C,if (∀ a∈S,rawMarkedPairRims P π d σ (markedRowRim a z)) ∧
    (∀ a∈J,rawMarkedPairSpokes π d σ g j a.1 z a.2) then 1 else 0

theorem rawMarkedRowCount_patterns (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ)
    (C : Finset V) (S : Finset (Bool×Bool×V)) (J : Finset (Bool×U))
    (g : Γ) (j : Color) (σ : RawMarkedOutcome V U Γ Color) :
    rawMarkedRowCount P π d C S J g j σ=
      rawMarkedPatternSum P π d (fun z : C=>markedRowResources S J z.val) (fun _=>1) g j σ := by
  unfold rawMarkedRowCount rawMarkedPatternSum supportedPatternSum
  rw [Finset.sum_coe_sort C (fun z : V=>(1:ℝ)*patternValue (markedRowResources S J z)
    (fun _=>true) (typedMarkedResourceState (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j)))]
  apply Finset.sum_congr rfl
  intro z hz
  rw [one_mul,patternValue_indicator]
  congr 1
  simp only [markedRowResources,Finset.forall_mem_union,Finset.forall_mem_image,
    typedMarkedResourceState,Sum.elim_inl,Sum.elim_inr,decide_eq_true_eq]

theorem markedRowRim_marginal (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ)
    (p k : ℝ) (q : U→Γ→ℝ) (s : U→Color→ℝ) (g : Γ) (j : Color)
    (a : Bool×Bool×V) (z : V) (ha : markedRowEligible P π (3*d) a z) :
    rawMarkedWheelMarginal P π d p k q s g j (Sum.inl (markedRowRim a z))=if a.1 then k else p := by
  obtain ⟨b,c,x⟩ := a
  cases b <;> cases c <;>
    simp only [markedRowEligible,markedRowRim,Bool.false_eq_true,ite_false,ite_true,
      Sum.elim_inl,Sum.elim_inr] at ha ⊢ <;>
    simp only [rawMarkedWheelMarginal,ha.1,ha.2,permutationClose_symm π (3*d),
      not_false_eq_true,true_and,ite_true] <;>
    simp only [show ¬PermutationClose π (3*d) z x from fun h=>ha.1 ((permutationClose_symm π (3*d) z x).mp h),not_false_eq_true,and_self,ite_true]

theorem markedRowResources_target (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ)
    (p k : ℝ) (q : U→Γ→ℝ) (s : U→Color→ℝ) (g : Γ) (j : Color)
    (S : Finset (Bool×Bool×V)) (J : Finset (Bool×U)) (z : V)
    (hel : ∀ a∈S,markedRowEligible P π (3*d) a z)
    (hphys : Set.InjOn (fun a=>markedPairPhysical π (markedRowRim a z)) S) :
    (∏ e∈markedRowResources S J z,rawMarkedWheelMarginal P π d p k q s g j e)=
      (∏ a∈S,if a.1 then k else p)*(∏ a∈J,if a.1 then q a.2 g else s a.2 j) := by
  unfold markedRowResources
  rw [Finset.prod_union (by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp he
    obtain ⟨b,hb,hf⟩ := Finset.mem_image.mp hf
    have hh := he.trans hf.symm
    cases hh)]
  rw [Finset.prod_image (by
    intro a ha b hb he
    exact hphys ha hb (congrArg (markedPairPhysical π) (Sum.inl.inj he)))]
  rw [Finset.prod_image (by
    intro a ha b hb he
    have he' := Sum.inr.inj he
    exact Prod.ext (congrArg (fun e : Bool×V×U=>e.1) he')
      (congrArg (fun e : Bool×V×U=>e.2.2) he'))]
  apply congrArg₂ (fun x y : ℝ=>x*y)
  · exact Finset.prod_congr rfl (fun a ha=>markedRowRim_marginal P π d p k q s g j a z (hel a ha))
  · exact Finset.prod_congr rfl (fun a _=>rfl)

theorem rawMarkedRowCount_tail
    (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1)
    (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (A : Finset V) (hA : A.Nonempty) (S T : Finset (Bool×Bool×V)) (J : Finset (Bool×U))
    (hJ : Set.InjOn (fun a : Bool×U=>a.2) J)
    (h : ℕ) (hsize : S.card+J.card≤h) (g : Γ) (j : Color) (t : ℝ) (ht : 0<t) :
    (FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)).probability
      (fun σ=>t≤|rawMarkedRowCount P π d (markedRowDomain P π (3*d) A S T) S J g j σ-
        (∏ a∈S,if a.1 then k else p)*(∏ a∈J,if a.1 then q a.2 g else s a.2 j)*
          (markedRowDomain P π (3*d) A S T).card|)≤
      2*Real.exp (-2*t^2/((8*(d:ℝ)+6)^2*(2*((h:ℝ)+1)*A.card))) := by
  let C := markedRowDomain P π (3*d) A S T
  have hdom (z : C) := (Finset.mem_filter.mp z.property).2
  have hdisj (z : C) := markedRowResources_disjoint π d S J z.val (hdom z).2.1 hJ
  have hh := rawMarkedPatternSum_tail P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort
    (fun z : C=>markedRowResources S J z.val) (fun _=>1) (by intro _;norm_num) (fun z a ha b hb hab=>hdisj z a b ha hb hab) g j
    2 ((h:ℝ)+1) A.card (by norm_num) (by positivity) (by exact_mod_cast hA.card_pos)
    (by
      intro z
      have hh := (markedRowResources_card S J z.val).trans hsize
      have hh' : ((markedRowResources S J z.val).card:ℝ)≤h := by exact_mod_cast hh
      linarith)
    (by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,Fintype.card_coe]
      exact_mod_cast Finset.card_filter_le A _)
    (fun e=>markedRowResources_load S J C e) t ht
  have hmean : (∑ z : C,(1:ℝ)*∏ e∈markedRowResources S J z.val,rawMarkedWheelMarginal P π d p k q s g j e)=
      (∏ a∈S,if a.1 then k else p)*(∏ a∈J,if a.1 then q a.2 g else s a.2 j)*C.card := by
    simp_rw [one_mul,markedRowResources_target P π d p k q s g j S J _ (hdom _).1 (hdom _).2.1]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_coe]
    ring
  rw [hmean] at hh
  simpa only [rawMarkedRowCount_patterns,C] using hh

end Oberwolfach
