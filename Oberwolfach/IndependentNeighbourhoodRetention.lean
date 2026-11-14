module

public import Oberwolfach.ColouredTwoPaths
public import Oberwolfach.EdgeRetention
public import Oberwolfach.EndpointRelativeCounts
public import Oberwolfach.BoundedFinsetCardinality
public import Oberwolfach.ConfigurationFailureMargins

@[expose] public section

/-! Fresh independent retention of physical graph edges. A single event
controls common neighbourhoods at every bounded root set, including roots
outside the fixed counting domain. Each undirected edge is sampled once. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem retained_common_neighbourhood_patterns (G:SimpleGraph V) (A T:Finset V)
    (σ:Sym2 V→Bool):
    ((common A T (fun v=>(retainedGraph G σ).neighborFinset v)).card:ℝ)=
      ∑ v∈common A T (fun x=>G.neighborFinset x),patternValue (T.image (fun x=>s(x,v))) (fun _=>true) σ:=by
  have he:common A T (fun v=>(retainedGraph G σ).neighborFinset v)=
      (common A T (fun x=>G.neighborFinset x)).filter (fun v=>∀ x∈T,σ s(x,v)=true):=by
    ext v
    simp only [mem_common_iff,Finset.mem_filter,SimpleGraph.mem_neighborFinset,retainedGraph]
    aesop
  rw [he,Finset.card_filter,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [patternValue_indicator]
  simp only [Nat.cast_ite,Nat.cast_one,Nat.cast_zero,Finset.forall_mem_image]

theorem common_neighbourhood_patterns_disjoint (G:SimpleGraph V) (A T:Finset V):
    ∀ v∈common A T (fun x=>G.neighborFinset x),∀ w∈common A T (fun x=>G.neighborFinset x),v≠w→
      Disjoint (T.image (fun x=>s(x,v))) (T.image (fun x=>s(x,w))):=by
  intro v hv w hw hvw
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp he
  obtain ⟨y,hy,hxy⟩:=Finset.mem_image.mp hf
  have hyv:G.Adj y v:=(G.mem_neighborFinset _ _).mp (((mem_common_iff A T _ v).mp hv).2 y hy)
  rcases Sym2.eq_iff.mp hxy with ⟨h1,h2⟩|⟨h1,h2⟩
  · exact hvw h2.symm
  · exact hyv.ne h1

theorem retained_common_neighbourhood_tail (G:SimpleGraph V) (A T:Finset V)
    (τ:ℝ) (hτ:0≤τ) (hτ1:τ≤1) (h:ℕ) (hsize:T.card≤h)
    (n t:ℝ) (hA:(A.card:ℝ)≤n) (hn:0<n) (ht:0<t):
    (FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.retentionCoin τ hτ hτ1)).probability
      (fun σ=>t≤|((common A T (fun v=>(retainedGraph G σ).neighborFinset v)).card:ℝ)-
        τ^T.card*(common A T (fun x=>G.neighborFinset x)).card|)≤
      2*Real.exp (-2*t^2/(n*(h+1))):=by
  by_cases hT:T=∅
  · subst T
    simp only [common,Finset.notMem_empty,false_implies,implies_true,Finset.filter_true,
      Finset.card_empty,pow_zero,one_mul,sub_self,abs_zero,not_le.mpr ht]
    rw [finiteLaw_probability_false]
    positivity
  have hk:0<T.card:=Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hT)
  have hpattern (v:V): (T.image (fun x=>s(x,v))).card=T.card:=by
    apply Finset.card_image_of_injective
    intro x y hxy
    exact incidentPair_injective v (by simpa only [Sym2.eq_swap] using hxy)
  have hCA:((common A T (fun x=>G.neighborFinset x)).card:ℝ)≤n:=by
    apply le_trans _ hA
    exact_mod_cast (Finset.card_le_card (show common A T (fun x=>G.neighborFinset x)⊆A from
      fun v hv=>((mem_common_iff A T _ v).mp hv).1))
  have hh:=finiteLaw_fixed_size_patterns_tail_at_scale
    (fun _:Sym2 V=>FiniteLaw.retentionCoin τ hτ hτ1)
    (common A T (fun x=>G.neighborFinset x)) (fun v=>T.image (fun x=>s(x,v))) (fun _ _=>true)
    T.card hk (fun v _=>hpattern v) (common_neighbourhood_patterns_disjoint G A T)
    (n:=n) (t:=t)
    hCA ht.le
  have hm:(∑ v∈common A T (fun x=>G.neighborFinset x),
      ∏ e∈T.image (fun x=>s(x,v)),(FiniteLaw.retentionCoin τ hτ hτ1).mass true)=
      τ^T.card*(common A T (fun x=>G.neighborFinset x)).card:=by
    simp only [FiniteLaw.retentionCoin,Bool.true_eq,ite_true,Finset.prod_const,hpattern,
      Finset.sum_const,nsmul_eq_mul,mul_comm]
  simp only [hm,←retained_common_neighbourhood_patterns G A T] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have hd:n*(T.card:ℝ)≤n*((h:ℝ)+1):=by
    have hs:(T.card:ℝ)≤h:=Nat.cast_le.mpr hsize
    nlinarith only [hs,hn]
  have hdpos:0<n*(T.card:ℝ):=mul_pos hn (Nat.cast_pos.mpr hk)
  simpa only [neg_div,neg_mul] using neg_le_neg
    (div_le_div_of_nonneg_left (show 0≤2*t^2 by positivity) hdpos hd)


theorem retained_common_neighbourhoods_common_event (h q:ℕ) (ε:ℝ) (hε:0<ε):
    ∃ N:ℕ,∀ (V:Type) [Fintype V] [DecidableEq V],N≤Fintype.card V→
    ∀ (G:SimpleGraph V) (s:ℕ),s≤Fintype.card V→∀ (A:Fin s→Finset V)
      (τ:ℝ) (hτ:0≤τ) (hτ1:τ≤1),
    1-1/(Fintype.card V:ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.retentionCoin τ hτ hτ1)).probability
        (fun σ=>∀ i,∀ T:Finset V,T.card≤h→
          |((common (A i) T (fun v=>(retainedGraph G σ).neighborFinset v)).card:ℝ)-
            τ^T.card*(common (A i) T (fun v=>G.neighborFinset v)).card|<ε*Fintype.card V):=by
  obtain ⟨N,hN⟩:=linear_deviation_failure_eventually_small ((2:ℝ)^h) (h+1) ε (by positivity) hε (h+1) q
  refine ⟨max 1 N,?_⟩
  intro V _ _ hn G s hs A τ hτ hτ1
  have hn0:0<Fintype.card V:=by omega
  have hnR:(0:ℝ)<Fintype.card V:=Nat.cast_pos.mpr hn0
  let I:=Fin s×{T:Finset V//T.card≤h}
  let μ:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.retentionCoin τ hτ hτ1)
  let Bad:=fun (i:I) (σ:Sym2 V→Bool)=>ε*Fintype.card V≤
    |((common (A i.1) i.2.val (fun v=>(retainedGraph G σ).neighborFinset v)).card:ℝ)-
      τ^i.2.val.card*(common (A i.1) i.2.val (fun v=>G.neighborFinset v)).card|
  let err:=2*Real.exp (-2*(ε*Fintype.card V)^2/((Fintype.card V:ℝ)*(h+1)))
  have htail (i:I):μ.probability (Bad i)≤err:=
    retained_common_neighbourhood_tail G (A i.1) i.2.val τ hτ hτ1 h i.2.property
      (Fintype.card V) (ε*Fintype.card V) (Nat.cast_le.mpr (Finset.card_le_univ _)) hnR (mul_pos hε hnR)
  have hcount:(Fintype.card I:ℝ)≤(2:ℝ)^h*(Fintype.card V:ℝ)^(h+1):=by
    have hc:Fintype.card I≤Fintype.card V*(Fintype.card V+1)^h:=by
      rw [Fintype.card_prod,Fintype.card_fin]
      exact Nat.mul_le_mul hs (boundedFinset_card h)
    have hn1:(Fintype.card V+1:ℝ)≤2*Fintype.card V:=by
      have ht:(1:ℝ)≤Fintype.card V:=by exact_mod_cast hn0
      linarith only [ht]
    have hpow:=pow_le_pow_left₀ (show (0:ℝ)≤Fintype.card V+1 by positivity) hn1 h
    calc
      _≤(Fintype.card V:ℝ)*(Fintype.card V+1:ℝ)^h:=by exact_mod_cast hc
      _≤(Fintype.card V:ℝ)*(2*Fintype.card V:ℝ)^h:=mul_le_mul_of_nonneg_left hpow hnR.le
      _=_:=by rw [mul_pow,pow_succ];ring
  have hsmall:=hN (Fintype.card V) (by omega) (Fintype.card I)
    ((Fintype.card V:ℝ)*(h+1)) (Nat.cast_nonneg _) hcount (by positivity) (by ring_nf;exact le_rfl)
  have hh:=finiteLaw_common_event_lower μ Finset.univ Bad (fun _=>err) (fun i _=>htail i)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,true_implies] at hh
  apply ((sub_le_sub_left hsmall 1).trans hh).trans
  apply finiteLaw_probability_mono
  intro σ hσ i T hT
  exact not_le.mp (hσ (i,⟨T,hT⟩))

end Oberwolfach
