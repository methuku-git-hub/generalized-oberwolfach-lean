module

public import Oberwolfach.ExpandedUnassignedColumnLocalSmallFailure
public import Oberwolfach.FiniteSigmaSameFirstEvent
public import Oberwolfach.FiniteLawIntersectionLower

@[expose] public section

/-! Local unassigned-spoke counts can be attached to any earlier event on
the expanded sample, including a dependent matching construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_local_unassigned_columns_on_prior
    (d:ℕ) (hd:2≤d) (χ:ℝ) (hχ:0<χ):
    ∃M:ℕ,1≤M ∧ ∀(V U Γ Color:Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
      [Fintype Γ] [Fintype Color],
    ∀(A:Finset V) (B:Finset U),M≤A.card→0<B.card→B.card≤A.card→
    ∀(π:Equiv.Perm V) (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀ω,Fintype (R ω)] (ν:∀ω,FiniteLaw (R ω)) (E:(Σω,R ω)→Prop) (loss:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-loss≤(μ.sigma ν).probability E →
    1-(loss+χ)≤(μ.sigma ν).probability (fun z=>E z ∧ ∀v∈A,
      |rawIntervalUnassignedColumnCount π d (fun e=>z.1 (Sum.inr e)) v B-
        ∑w∈B,(1-(∑g,q w g)-(∑j,s w j))|<(A.card:ℝ)^(3/4:ℝ)) :=by
  obtain ⟨M,hM,hbase⟩:=raw_expanded_unassigned_column_local_family_small_failure d hd χ hχ
  refine ⟨M,hM,?_⟩
  intro V U Γ Color _ _ _ _ _ _ A B hA hB hBA π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum
    q hq hQ s hs hS hnoshort R _ ν E loss μ hE
  let P:=fun ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e=>
    ∀v∈A,|rawIntervalUnassignedColumnCount π d (fun e=>ω (Sum.inr e)) v B-
      ∑w∈B,(1-(∑g,q w g)-(∑j,s w j))|<(A.card:ℝ)^(3/4:ℝ)
  let νunit:=fun (_:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)=>FiniteLaw.uniform Unit
  have hlocal:1-χ≤(μ.sigma νunit).probability (fun z=>P z.1):=by
    have hh:=hbase V U Γ Color Unit Finset.univ (fun _=>A) (fun _=>B)
      (by intro i hi; exact hA) (by intro i hi j hj h; cases i;cases j;rfl)
      (by intro i hi; exact hB) (by intro i hi; exact hBA) π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort
      (fun _=>Unit) (fun _=>FiniteLaw.uniform Unit)
    simpa only [P,Finset.mem_univ,true_implies,forall_const] using hh
  rw [finiteLaw_sigma_same_first_event μ νunit ν P] at hlocal
  simpa only [P,sub_add_eq_sub_sub] using
    finiteLaw_intersection_lower (μ.sigma ν) E (fun z=>P z.1) loss χ hE hlocal
end Oberwolfach
