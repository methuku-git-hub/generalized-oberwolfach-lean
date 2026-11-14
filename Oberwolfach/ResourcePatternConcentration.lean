module

public import Oberwolfach.FiniteCoordinateIndependence
public import Oberwolfach.ResourceRootOmittedLoads

@[expose] public section

/-! Concentration of fixed resource-pattern loads with a specified coordinate
omitted. Patterns may require different categorical states; their supports,
coefficients and root domains are fixed before sampling. The variance bound
uses the actual pair weights rather than the number of sample coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A]

def resourcePatternLoad {State : A → Type*} (R : I → Finset A) (w : I → ℝ)
    (s : I → ∀ a,State a) (e : A) (σ : ∀ a,State a) : ℝ :=
  ∑ i,(if e∈R i then w i else 0)*patternValue (R i\{e}) (s i) σ

def resourcePatternMean {State : A → Type*} [∀ a,Fintype (State a)]
    (μ : ∀ a,FiniteLaw (State a)) (R : I → Finset A) (w : I → ℝ)
    (s : I → ∀ a,State a) (e : A) : ℝ :=
  ∑ i,(if e∈R i then w i else 0)*∏ a∈R i\{e},(μ a).mass (s i a)

theorem resourcePatternLoad_expectation {State : A → Type*} [∀ a,Fintype (State a)]
    (μ : ∀ a,FiniteLaw (State a)) (R : I → Finset A) (w : I → ℝ)
    (s : I → ∀ a,State a) (e : A) :
    (FiniteLaw.pi μ).expectation (resourcePatternLoad R w s e)=resourcePatternMean μ R w s e := by
  exact finiteLaw_expectation_omitted_root_sum μ Finset.univ R {e} s
    (fun i=>if e∈R i then w i else 0)

theorem resourceOmittedPairWeight_nonneg (R : I → Finset A) (w : I → ℝ)
    (hw : ∀ i,0≤w i) (e f : A) : 0≤resourceOmittedPairWeight R w e f := by
  exact Finset.sum_nonneg (fun i _=>by split_ifs <;> first | exact hw i | rfl)

theorem resourceOmittedPairWeight_sum (R : I → Finset A) (w : I → ℝ) (e : A) :
    (∑ f,resourceOmittedPairWeight R w e f)=
      ∑ i,if e∈R i then ((R i\{e}).card:ℝ)*w i else 0 := by
  unfold resourceOmittedPairWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases he : e∈R i
  · simp only [he,true_and,ite_true]
    rw [← Finset.sum_filter]
    have hset : Finset.univ.filter (fun f=>f∈R i ∧ f≠e)=R i\{e} := by ext f;simp
    rw [hset]
    simp only [Finset.sum_const,nsmul_eq_mul]
  · simp only [he,false_and,ite_false,Finset.sum_const_zero]

theorem resourceOmittedPairWeight_square_sum_le (R : I → Finset A) (w : I → ℝ)
    (hw : ∀ i,0≤w i) (e : A) (q L a : ℝ)
    (hq : 0≤q) (ha : 0≤a)
    (hsize : ∀ i,e∈R i → ((R i\{e}).card:ℝ)≤q)
    (hload : (∑ i,if e∈R i then w i else 0)≤L)
    (hpair : ∀ f,resourceOmittedPairWeight R w e f≤a) :
    (∑ f,(resourceOmittedPairWeight R w e f)^2)≤a*q*L := by
  have htotal : (∑ f,resourceOmittedPairWeight R w e f)≤q*L := by
    rw [resourceOmittedPairWeight_sum]
    calc
      _ ≤ ∑ i,q*(if e∈R i then w i else 0) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases he : e∈R i
        · simp only [he,ite_true]
          exact mul_le_mul_of_nonneg_right (hsize i he) (hw i)
        · simp only [he,ite_false,mul_zero,le_refl]
      _ = q*∑ i,if e∈R i then w i else 0 := (Finset.mul_sum _ _ _).symm
      _ ≤ q*L := mul_le_mul_of_nonneg_left hload hq
  calc
    _ ≤ ∑ f,a*resourceOmittedPairWeight R w e f := by
      apply Finset.sum_le_sum
      intro f _
      simpa only [pow_two] using mul_le_mul_of_nonneg_right (hpair f)
        (resourceOmittedPairWeight_nonneg R w hw e f)
    _ = a*∑ f,resourceOmittedPairWeight R w e f := (Finset.mul_sum _ _ _).symm
    _ ≤ a*(q*L) := mul_le_mul_of_nonneg_left htotal ha
    _ = _ := by ring

theorem resourcePatternLoad_one_coordinate {State : A → Type*}
    (R : I → Finset A) (w : I → ℝ) (hw : ∀ i,0≤w i)
    (s : I → ∀ a,State a) (e f : A) (σ τ : ∀ a,State a)
    (hagree : ∀ a,a≠f → σ a=τ a) :
    |resourcePatternLoad R w s e σ-resourcePatternLoad R w s e τ|≤
      resourceOmittedPairWeight R w e f := by
  have hh := omitted_root_stability Finset.univ R {e} {f} s
    (fun i=>if e∈R i then w i else 0) τ σ
    (by intro i _;split_ifs <;> first | exact hw i | rfl)
    (by intro i _ a _ _ ha;exact (hagree a (by simpa using ha)).symm)
  simp only [Finset.sum_singleton] at hh
  apply hh.trans_eq
  unfold resourceOmittedPairWeight
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.mem_sdiff,Finset.mem_singleton]
  split_ifs <;> simp_all

/-- This form also covers a zero actual influence sum: the positive supplied
upper bound does not conceal a division by zero. -/
theorem finiteLaw_boundedDifferences_variance_bound
    {State : A → Type*} [∀ a,Fintype (State a)]
    (μ : ∀ a,FiniteLaw (State a)) (X : (∀ a,State a) → ℝ)
    (c : A → ℝ) (hc : ∀ a,0≤c a) (v : ℝ) (hv : 0<v)
    (hsq : (∑ a,(c a)^2)≤v)
    (hchange : ∀ a σ τ,(∀ b,b≠a → σ b=τ b) → |X σ-X τ|≤c a)
    (t : ℝ) (ht : 0<t) :
    (FiniteLaw.pi μ).probability (fun σ=>t≤|X σ-(FiniteLaw.pi μ).expectation X|)≤
      2*Real.exp (-2*t^2/v) := by
  have hs0 : 0≤∑ a,(c a)^2 := Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  by_cases hs : (∑ a,(c a)^2)=0
  · have hc0 : ∀ a,c a=0 := by
      intro a
      have hh := Finset.single_le_sum (s:=Finset.univ) (f:=fun a=>(c a)^2)
        (fun _ _=>sq_nonneg _) (Finset.mem_univ a)
      rw [hs] at hh
      nlinarith only [hh,sq_nonneg (c a)]
    have hx := finiteLaw_zero_boundedDifferences μ X
      (fun a σ τ hagree=>by simpa only [hc0 a] using hchange a σ τ hagree)
    have hbad : ∀ σ,¬t≤|X σ-(FiniteLaw.pi μ).expectation X| := by
      intro σ;rw [hx σ,sub_self,abs_zero];exact not_le.mpr ht
    simp only [FiniteLaw.probability,hbad,ite_false,Finset.sum_const_zero]
    positivity
  · have hsp : 0<(∑ a,(c a)^2) := lt_of_le_of_ne hs0 (Ne.symm hs)
    apply (finiteLaw_boundedDifferences μ X c hc hchange ht.le).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    exact (div_le_div_iff₀ hsp hv).mpr
      (mul_le_mul_of_nonpos_left hsq (by nlinarith only [sq_nonneg t]))

theorem resourcePatternLoad_tail {State : A → Type*} [∀ a,Fintype (State a)]
    (μ : ∀ a,FiniteLaw (State a)) (R : I → Finset A) (w : I → ℝ)
    (hw : ∀ i,0≤w i) (s : I → ∀ a,State a) (e : A)
    (q L a : ℝ) (hq : 0<q) (hL : 0<L) (ha : 0<a)
    (hsize : ∀ i,e∈R i → ((R i\{e}).card:ℝ)≤q)
    (hload : (∑ i,if e∈R i then w i else 0)≤L)
    (hpair : ∀ f,resourceOmittedPairWeight R w e f≤a)
    (t : ℝ) (ht : 0<t) :
    (FiniteLaw.pi μ).probability (fun σ=>t≤|resourcePatternLoad R w s e σ-resourcePatternMean μ R w s e|)≤
      2*Real.exp (-2*t^2/(a*q*L)) := by
  have hh := finiteLaw_boundedDifferences_variance_bound μ (resourcePatternLoad R w s e)
    (resourceOmittedPairWeight R w e) (resourceOmittedPairWeight_nonneg R w hw e)
    (a*q*L) (by positivity)
    (resourceOmittedPairWeight_square_sum_le R w hw e q L a hq.le ha.le hsize hload hpair)
    (resourcePatternLoad_one_coordinate R w hw s e) t ht
  simpa only [resourcePatternLoad_expectation] using hh

theorem resourcePatternLoad_common_event {State : A → Type*} [∀ a,Fintype (State a)]
    (μ : ∀ a,FiniteLaw (State a)) (R : I → Finset A) (w : I → ℝ)
    (hw : ∀ i,0≤w i) (s : I → ∀ a,State a) (q L a : ℝ)
    (hq : 0<q) (hL : 0<L) (ha : 0<a)
    (hsize : ∀ i,((R i).card:ℝ)≤q)
    (hload : ∀ e,(∑ i,if e∈R i then w i else 0)≤L)
    (hpair : ∀ e f,resourceOmittedPairWeight R w e f≤a)
    (t : ℝ) (ht : 0<t) :
    1-(Fintype.card A:ℝ)*(2*Real.exp (-2*t^2/(a*q*L)))≤
      (FiniteLaw.pi μ).probability (fun σ=>∀ e,
        |resourcePatternLoad R w s e σ-resourcePatternMean μ R w s e|<t) := by
  have hh := finiteLaw_common_event_lower (FiniteLaw.pi μ) Finset.univ
    (fun e σ=>t≤|resourcePatternLoad R w s e σ-resourcePatternMean μ R w s e|)
    (fun _=>2*Real.exp (-2*t^2/(a*q*L)))
    (fun e _=>resourcePatternLoad_tail μ R w hw s e q L a hq hL ha
      (fun i _=>by
        have hc : ((R i\{e}).card:ℝ)≤(R i).card := by
          exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : R i\{e}⊆R i)
        exact hc.trans (hsize i))
      (hload e) (hpair e) t ht)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,true_implies,not_le] using hh


/-- A sparse incidence relation between primitive coordinates and resource
states costs the product of its two maximum incidence bounds. -/
theorem locality_square_sum {E : Type*} [Fintype E] [DecidableEq E]
    (S : A → Finset E) (B : ℝ) (hB : 0≤B)
    (hread : ∀ a,((S a).card:ℝ)≤B)
    (haffect : ∀ e,((Finset.univ.filter (fun a=>e∈S a)).card:ℝ)≤B)
    (c : A → ℝ) :
    (∑ e,(∑ a,if e∈S a then c a else 0)^2)≤B^2*∑ a,(c a)^2 := by
  have hlocal (e : E) : (∑ a,if e∈S a then c a else 0)^2≤
      B*∑ a,if e∈S a then (c a)^2 else 0 := by
    rw [← Finset.sum_filter,← Finset.sum_filter]
    have hh := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ.filter (fun a=>e∈S a)) (fun _ : A=>(1:ℝ)) c
    simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (haffect e)
      (Finset.sum_nonneg (fun _ _=>sq_nonneg _)))
  calc
    _ ≤ ∑ e,B*∑ a,if e∈S a then (c a)^2 else 0 := Finset.sum_le_sum (fun e _=>hlocal e)
    _ = B*∑ a,((S a).card:ℝ)*(c a)^2 := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_filter]
      have hs : Finset.univ.filter (fun e=>e∈S a)=S a := by ext;simp
      rw [hs,Finset.sum_const,nsmul_eq_mul]
    _ ≤ B*∑ a,B*(c a)^2 := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun a _=>mul_le_mul_of_nonneg_right (hread a) (sq_nonneg _))) hB
    _ = _ := by rw [← Finset.mul_sum];ring

theorem resourcePatternLoad_supported_change
    {E : Type*} [Fintype E] [DecidableEq E] {Base : E → Type*} {State : A → Type*}
    (R : I → Finset A) (w : I → ℝ) (hw : ∀ i,0≤w i)
    (s : I → ∀ a,State a) (S : A → Finset E)
    (state : (∀ e,Base e) → ∀ a,State a)
    (hs : ∀ a σ τ,(∀ e∈S a,σ e=τ e) → state σ a=state τ a)
    (root : A) (e : E) (σ τ : ∀ e,Base e)
    (hagree : ∀ f,f≠e → σ f=τ f) :
    |resourcePatternLoad R w s root (state σ)-resourcePatternLoad R w s root (state τ)|≤
      ∑ a,if e∈S a then resourceOmittedPairWeight R w root a else 0 := by
  let D := Finset.univ.filter (fun a=>e∈S a)
  have hh := omitted_root_stability Finset.univ R {root} D s
    (fun i=>if root∈R i then w i else 0) (state τ) (state σ)
    (by intro i _;split_ifs <;> first | exact hw i | rfl)
    (by
      intro i _ a _ _ ha
      apply hs a
      intro f hf
      apply Eq.symm (hagree f _)
      intro he;subst f
      exact ha (by simp [D,hf]))
  apply hh.trans_eq
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : e∈S a
  · simp only [ha,ite_true,resourceOmittedPairWeight]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Finset.mem_sdiff,Finset.mem_singleton]
    split_ifs <;> simp_all
  · simp only [ha,ite_false]

theorem resourcePatternLoad_supported_tail
    {E : Type*} [Fintype E] [DecidableEq E]
    {Base : E → Type*} [∀ e,Fintype (Base e)] {State : A → Type*}
    (μ : ∀ e,FiniteLaw (Base e)) (R : I → Finset A) (w : I → ℝ)
    (hw : ∀ i,0≤w i) (s : I → ∀ a,State a)
    (S : A → Finset E) (state : (∀ e,Base e) → ∀ a,State a)
    (hs : ∀ a σ τ,(∀ e∈S a,σ e=τ e) → state σ a=state τ a)
    (B : ℝ) (hB : 0<B)
    (hread : ∀ a,((S a).card:ℝ)≤B)
    (haffect : ∀ e,((Finset.univ.filter (fun a=>e∈S a)).card:ℝ)≤B)
    (root : A) (q L a : ℝ) (hq : 0<q) (hL : 0<L) (ha : 0<a)
    (hsize : ∀ i,root∈R i → ((R i\{root}).card:ℝ)≤q)
    (hload : (∑ i,if root∈R i then w i else 0)≤L)
    (hpair : ∀ f,resourceOmittedPairWeight R w root f≤a)
    (t : ℝ) (ht : 0<t) :
    (FiniteLaw.pi μ).probability (fun σ=>t≤
      |resourcePatternLoad R w s root (state σ)-
        (FiniteLaw.pi μ).expectation (fun τ=>resourcePatternLoad R w s root (state τ))|)≤
      2*Real.exp (-2*t^2/(B^2*a*q*L)) := by
  apply finiteLaw_boundedDifferences_variance_bound μ
    (fun σ=>resourcePatternLoad R w s root (state σ))
    (fun e=>∑ f,if e∈S f then resourceOmittedPairWeight R w root f else 0)
    (fun e=>Finset.sum_nonneg (fun f _=>by
      split_ifs;exact resourceOmittedPairWeight_nonneg R w hw root f;exact le_refl _))
    (B^2*a*q*L) (by positivity) _
    (resourcePatternLoad_supported_change R w hw s S state hs root) t ht
  calc
    _ ≤ B^2*∑ f,(resourceOmittedPairWeight R w root f)^2 := locality_square_sum S B hB.le hread haffect _
    _ ≤ B^2*(a*q*L) := mul_le_mul_of_nonneg_left
      (resourceOmittedPairWeight_square_sum_le R w hw root q L a hq.le ha.le hsize hload hpair) (sq_nonneg _)
    _ = _ := by ring


theorem finiteLaw_disjoint_supported_family
    {E J : Type*} [Fintype E] [DecidableEq E] [DecidableEq J]
    {Base : E → Type*} [∀ e,Fintype (Base e)]
    (μ : ∀ e,FiniteLaw (Base e)) (S : J → Finset E)
    (event : J → (∀ e,Base e) → Prop)
    (hs : ∀ j σ τ,(∀ e∈S j,σ e=τ e) → (event j σ↔event j τ))
    (T : Finset J)
    (hdisj : ∀ i∈T,∀ j∈T,i≠j → Disjoint (S i) (S j)) :
    (FiniteLaw.pi μ).probability (fun σ=>∀ j∈T,event j σ)=
      ∏ j∈T,(FiniteLaw.pi μ).probability (event j) := by
  induction T using Finset.induction_on with
  | empty => simp [FiniteLaw.probability,(FiniteLaw.pi μ).total]
  | @insert j T hj ih =>
    have hd : Disjoint (S j) (T.biUnion S) := by
      apply Finset.disjoint_left.mpr
      intro e he ht
      obtain ⟨i,hi,hei⟩ := Finset.mem_biUnion.mp ht
      exact Finset.disjoint_left.mp
        (hdisj j (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)
          (fun h=>hj (h ▸ hi))) he hei
    have htail : ∀ σ τ,(∀ e∈T.biUnion S,σ e=τ e) →
        ((∀ i∈T,event i σ)↔∀ i∈T,event i τ) := by
      intro σ τ hagree
      apply forall_congr'
      intro i
      apply forall_congr'
      intro hi
      exact hs i σ τ (fun e he=>hagree e (Finset.mem_biUnion.mpr ⟨i,hi,he⟩))
    have hh := finiteLaw_disjoint_supported_events μ (S j) (T.biUnion S) hd
      (event j) (fun σ=>∀ i∈T,event i σ) (hs j) htail
    have hi := ih (fun i hi j hj hne=>hdisj i (Finset.mem_insert_of_mem hi)
      j (Finset.mem_insert_of_mem hj) hne)
    simpa only [Finset.forall_mem_insert,Finset.prod_insert hj,hi] using hh

/-- Expected potential loads factor on each candidate when its non-root
resource states read disjoint primitive coordinates. Nothing conditions the
experiment on the omitted root, whose coordinate support may overlap them. -/
theorem resourcePatternLoad_supported_expectation
    {E : Type*} [Fintype E] [DecidableEq E]
    {Base : E → Type*} [∀ e,Fintype (Base e)] {State : A → Type*}
    (μ : ∀ e,FiniteLaw (Base e)) (R : I → Finset A) (w : I → ℝ)
    (s : I → ∀ a,State a) (S : A → Finset E)
    (state : (∀ e,Base e) → ∀ a,State a)
    (hs : ∀ a σ τ,(∀ e∈S a,σ e=τ e) → state σ a=state τ a)
    (root : A)
    (hdisj : ∀ i,root∈R i → ∀ a∈R i\{root},∀ b∈R i\{root},a≠b → Disjoint (S a) (S b)) :
    (FiniteLaw.pi μ).expectation (fun σ=>resourcePatternLoad R w s root (state σ))=
      ∑ i,(if root∈R i then w i else 0)*∏ a∈R i\{root},
        (FiniteLaw.pi μ).probability (fun σ=>state σ a=s i a) := by
  unfold FiniteLaw.expectation resourcePatternLoad
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : root∈R i
  · simp only [hi,ite_true]
    have hh := finiteLaw_disjoint_supported_family μ S (fun a σ=>state σ a=s i a)
      (fun a σ τ hagree=>by rw [hs a σ τ hagree]) (R i\{root}) (hdisj i hi)
    rw [← hh]
    unfold FiniteLaw.probability
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [patternValue_indicator]
    split_ifs <;> ring
  · simp only [hi,ite_false,zero_mul,mul_zero,Finset.sum_const_zero]

end Oberwolfach
