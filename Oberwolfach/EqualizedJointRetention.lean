module

public import Oberwolfach.EqualizedColourRetention
public import Oberwolfach.JointColourRetention
public import Oberwolfach.FiniteUnionOverlap

@[expose] public section

/-! The exact overlap correction in a joint retention probability.
Overlapping avoidance requirements are not treated as independent. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem equalized_joint_retention
    {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C]
    (G : SimpleGraph V) (L : V → Finset C) (hL : ∀ v,(L v).Nonempty)
    {l K : ℕ} (hl : 1<l) (hcard : ∀ v,(L v).card=l)
    (S : Finset V) (hS : ∀ u∈S,∀ v∈S,¬G.Adj u v) (c : C)
    (hc : ∀ v∈S,c∈L v)
    (hbound : ∀ v∈S,(colourNeighbourSet G L v c).card≤K) :
    (FiniteLaw.pi (fun u=>(FiniteLaw.uniformOn (L u) (hL u)).withCoin
      (equalizationCoin G L l K u)
      (equalizationCoin_bounds G L (by omega) K u))).probability
      (fun σ=>∀ v∈S,coinRetainedColour G σ v=some c)=
      (((1-1/(l : ℝ))^K)/(l : ℝ))^S.card/
        (1-1/(l : ℝ))^(finiteUnionOverlap S (fun v=>colourNeighbourSet G L v c)) := by
  classical
  let q : ℝ := 1-1/(l : ℝ)
  let N := fun v=>colourNeighbourSet G L v c
  have hq : 0<q := by
    have hlr : (1 : ℝ)<l := by exact_mod_cast hl
    have hpos : (0 : ℝ)<l := by positivity
    exact sub_pos.mpr ((div_lt_one hpos).mpr hlr)
  have havoid : (∏ u∈setNeighbours G S,
      (1-(FiniteLaw.uniformOn (L u) (hL u)).mass c))=q^(S.biUnion N).card := by
    have he : (setNeighbours G S).filter (fun u=>c∈L u)=S.biUnion N := by
      ext u
      simp only [Finset.mem_filter,setNeighbours,Finset.mem_univ,true_and,
        Finset.mem_biUnion,N,colourNeighbourSet]
      constructor
      · rintro ⟨⟨v,hv,hvu⟩,hcu⟩
        exact ⟨v,hv,hvu,hcu⟩
      · rintro ⟨v,hv,hvu,hcu⟩
        exact ⟨⟨v,hv,hvu⟩,hcu⟩
    have hp (u : V) : 1-(FiniteLaw.uniformOn (L u) (hL u)).mass c=
        if c∈L u then q else 1 := by
      by_cases hu : c∈L u <;> simp [FiniteLaw.uniformOn,hu,hcard,q]
    simp_rw [hp]
    rw [← Finset.prod_filter,he,Finset.prod_const]
  have hroot :
      (∏ v∈S,(FiniteLaw.uniformOn (L v) (hL v)).mass c*equalizationCoin G L l K v c)=
      (1/(l : ℝ))^S.card*q^(∑ v∈S,(K-(N v).card)) := by
    have hp (v : V) (hv : v∈S) :
        (FiniteLaw.uniformOn (L v) (hL v)).mass c*equalizationCoin G L l K v c=
          (1/(l : ℝ))*q^(K-(N v).card) := by
      simp only [FiniteLaw.uniformOn,hc v hv,ite_true,hcard,equalizationCoin,q,N]
    rw [Finset.prod_congr rfl hp,Finset.prod_mul_distrib,Finset.prod_const,
      Finset.prod_pow_eq_pow_sum]
  have hsum : (∑ v∈S,(K-(N v).card))+(∑ v∈S,(N v).card)=S.card*K := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _v∈S,K := Finset.sum_congr rfl (fun v hv=>Nat.sub_add_cancel (hbound v hv))
      _ = _ := by simp
  have hover := finiteUnionOverlap_add_union S N
  have hexp : ((∑ v∈S,(K-(N v).card))+(S.biUnion N).card)+finiteUnionOverlap S N=S.card*K := by
    omega
  rw [joint_coinRetention_probability G _ _ _ S hS c,hroot,havoid]
  change ((1/(l : ℝ))^S.card*q^(∑ v∈S,(K-(N v).card)))*q^(S.biUnion N).card=
    (q^K/(l : ℝ))^S.card/q^(finiteUnionOverlap S N)
  apply (eq_div_iff (pow_ne_zero _ hq.ne')).mpr
  calc
    _ = (1/(l : ℝ))^S.card*q^
        (((∑ v∈S,(K-(N v).card))+(S.biUnion N).card)+finiteUnionOverlap S N) := by
      rw [pow_add,pow_add]
      ring
    _ = (1/(l : ℝ))^S.card*q^(S.card*K) := by rw [hexp]
    _ = _ := by rw [Nat.mul_comm S.card K,pow_mul,div_pow];ring

end Oberwolfach
