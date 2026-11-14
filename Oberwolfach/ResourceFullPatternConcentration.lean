module

public import Oberwolfach.ResourcePatternConcentration

@[expose] public section
/-! Concentration of the full weight of a fixed candidate family, rather
than a root-omitted load. Supports may overlap between different candidates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A I:Type} [Fintype A] [Fintype I] [DecidableEq A]

def resourceFullPatternLoad {State:A→Type} (R:I→Finset A) (w:I→ℝ)
    (s:I→∀a,State a) (σ:∀a,State a):ℝ :=
  ∑i,w i*patternValue (R i) (s i) σ

def resourceFullIncidenceWeight (R:I→Finset A) (w:I→ℝ) (a:A):ℝ :=
  ∑i,if a∈R i then w i else 0

theorem resource_full_incidence_nonneg (R:I→Finset A) (w:I→ℝ)
    (hw:∀i,0≤w i) (a:A):0≤resourceFullIncidenceWeight R w a :=by
  exact Finset.sum_nonneg (fun i _=>by split_ifs <;> first | exact hw i | rfl)

theorem resource_full_incidence_sum (R:I→Finset A) (w:I→ℝ):
    (∑a,resourceFullIncidenceWeight R w a)=∑i,((R i).card:ℝ)*w i :=by
  unfold resourceFullIncidenceWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Finset.sum_filter]
  have he:Finset.univ.filter (fun a=>a∈R i)=R i:=by ext a;simp
  rw [he,Finset.sum_const,nsmul_eq_mul]

theorem resource_full_incidence_square_sum (R:I→Finset A) (w:I→ℝ)
    (hw:∀i,0≤w i) (q L a:ℝ) (hq:0≤q) (ha:0≤a)
    (hsize:∀i,((R i).card:ℝ)≤q) (htotal:(∑i,w i)≤L)
    (hinc:∀x,resourceFullIncidenceWeight R w x≤a):
    (∑x,(resourceFullIncidenceWeight R w x)^2)≤a*q*L :=by
  have hsum:(∑x,resourceFullIncidenceWeight R w x)≤q*L:=by
    rw [resource_full_incidence_sum]
    calc
      _ ≤ ∑i,q*w i :=Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_right (hsize i) (hw i))
      _ = q*∑i,w i :=(Finset.mul_sum _ _ _).symm
      _ ≤ q*L :=mul_le_mul_of_nonneg_left htotal hq
  calc
    _ ≤ ∑x,a*resourceFullIncidenceWeight R w x :=by
      apply Finset.sum_le_sum
      intro x _
      simpa only [pow_two] using mul_le_mul_of_nonneg_right (hinc x) (resource_full_incidence_nonneg R w hw x)
    _ = a*∑x,resourceFullIncidenceWeight R w x :=(Finset.mul_sum _ _ _).symm
    _ ≤ a*(q*L) :=mul_le_mul_of_nonneg_left hsum ha
    _ = _ :=by ring

theorem resource_full_pattern_supported_change
    {E:Type} [Fintype E] [DecidableEq E] {Base:E→Type} {State:A→Type}
    (R:I→Finset A) (w:I→ℝ) (hw:∀i,0≤w i) (s:I→∀a,State a)
    (S:A→Finset E) (state:(∀e,Base e)→∀a,State a)
    (hs:∀a σ τ,(∀e∈S a,σ e=τ e)→state σ a=state τ a)
    (e:E) (σ τ:∀e,Base e) (hagree:∀f,f≠e→σ f=τ f):
    |resourceFullPatternLoad R w s (state σ)-resourceFullPatternLoad R w s (state τ)|≤
      ∑a,if e∈S a then resourceFullIncidenceWeight R w a else 0 :=by
  let D:=Finset.univ.filter (fun a=>e∈S a)
  have hh:=omitted_root_stability Finset.univ R ∅ D s w (state τ) (state σ)
    (by intro i _;exact hw i) (by
      intro i _ a _ _ ha
      apply hs a
      intro f hf
      apply Eq.symm (hagree f _)
      intro he;subst f
      exact ha (by simp [D,hf]))
  simp only [Finset.sdiff_empty] at hh
  change |resourceFullPatternLoad R w s (state σ)-resourceFullPatternLoad R w s (state τ)|≤_ at hh
  apply hh.trans_eq
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha:e∈S a
  · simp only [ha,ite_true,resourceFullIncidenceWeight]
  · simp only [ha,ite_false]

theorem resource_full_pattern_supported_tail
    {E:Type} [Fintype E] [DecidableEq E] {Base:E→Type} [∀e,Fintype (Base e)] {State:A→Type}
    (μ:∀e,FiniteLaw (Base e)) (R:I→Finset A) (w:I→ℝ) (hw:∀i,0≤w i) (s:I→∀a,State a)
    (S:A→Finset E) (state:(∀e,Base e)→∀a,State a)
    (hs:∀a σ τ,(∀e∈S a,σ e=τ e)→state σ a=state τ a)
    (B:ℝ) (hB:0<B) (hread:∀a,((S a).card:ℝ)≤B)
    (haffect:∀e,((Finset.univ.filter (fun a=>e∈S a)).card:ℝ)≤B)
    (q L a:ℝ) (hq:0<q) (hL:0<L) (ha:0<a)
    (hsize:∀i,((R i).card:ℝ)≤q) (htotal:(∑i,w i)≤L)
    (hinc:∀x,resourceFullIncidenceWeight R w x≤a)
    (t:ℝ) (ht:0<t):
    (FiniteLaw.pi μ).probability (fun σ=>t≤
      |resourceFullPatternLoad R w s (state σ)-
        (FiniteLaw.pi μ).expectation (fun τ=>resourceFullPatternLoad R w s (state τ))|)≤
      2*Real.exp (-2*t^2/(B^2*a*q*L)) :=by
  apply finiteLaw_boundedDifferences_variance_bound μ
    (fun σ=>resourceFullPatternLoad R w s (state σ))
    (fun e=>∑a,if e∈S a then resourceFullIncidenceWeight R w a else 0)
    (fun e=>Finset.sum_nonneg (fun a _=>by
      split_ifs;exact resource_full_incidence_nonneg R w hw a;exact le_rfl))
    (B^2*a*q*L) (by positivity) _
    (resource_full_pattern_supported_change R w hw s S state hs) t ht
  calc
    _ ≤ B^2*∑a,(resourceFullIncidenceWeight R w a)^2 :=locality_square_sum S B hB.le hread haffect _
    _ ≤ B^2*(a*q*L) :=mul_le_mul_of_nonneg_left
      (resource_full_incidence_square_sum R w hw q L a hq.le ha.le hsize htotal hinc) (sq_nonneg _)
    _ = _ :=by ring
end Oberwolfach
