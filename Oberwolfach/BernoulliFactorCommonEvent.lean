module

public import Oberwolfach.BernoulliAbsorberSampling
public import Oberwolfach.ConfigurationFailureMargins

@[expose] public section

/-! A single Bernoulli vertex event for all original vertex roots, all
root sets of the fixed size, and every supplied class. Later alterations
are deterministic and are not added to the probability union bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type*} [Fintype V] [DecidableEq V]

theorem bernoulli_domain_size_tail (A:Finset V) (hn:0<Fintype.card V)
    (p:ℝ) (hp:0≤p) (hp1:p≤1) (ε:ℝ) (hε:0<ε):
    (FiniteLaw.pi (fun _:V=>FiniteLaw.retentionCoin p hp hp1)).probability
      (fun σ=>ε*Fintype.card V≤|((A∩bernoulliVertexSet σ).card:ℝ)-p*A.card|)≤
      2*Real.exp (-2*ε^2/(1/(Fintype.card V:ℝ))):=by
  let R:A→Finset V:=fun x=>{x.val}
  have hc (σ:V→Bool):Fintype.card {x:A // R x⊆bernoulliVertexSet σ}=(A∩bernoulliVertexSet σ).card:=by
    let f:{x:A // R x⊆bernoulliVertexSet σ}→{x:V // x∈A∩bernoulliVertexSet σ}:=
      fun x=>⟨x.val.val,Finset.mem_inter.mpr ⟨x.val.property,Finset.singleton_subset_iff.mp x.property⟩⟩
    let e:{x:A // R x⊆bernoulliVertexSet σ}≃{x:V // x∈A∩bernoulliVertexSet σ} :=
      { toFun := f
        invFun := fun x=>⟨⟨x.val,(Finset.mem_inter.mp x.property).1⟩,
          Finset.singleton_subset_iff.mpr (Finset.mem_inter.mp x.property).2⟩
        left_inv := fun _=>rfl
        right_inv := fun _=>rfl }
    simpa only [Fintype.card_coe] using Fintype.card_congr e
  have hK (v:V):Fintype.card {x:A // v∈R x}≤1:=by
    have hi:Function.Injective (fun _: {x:A // v∈R x}=>()):=by
      intro x y _
      apply Subtype.ext
      apply Subtype.ext
      exact (Finset.mem_singleton.mp x.property).symm.trans (Finset.mem_singleton.mp y.property)
    simpa only [Fintype.card_unit] using Fintype.card_le_of_injective _ hi
  have hnR:(0:ℝ)<Fintype.card V:=Nat.cast_pos.mpr hn
  have hh:=bernoulli_support_count_tail R 1 1 (fun _=>Finset.card_singleton _) hK p hp hp1
    (Fintype.card V) (ε*Fintype.card V) hnR (mul_pos hε hnR) (by norm_num)
  have he:-2*(ε*Fintype.card V)^2/(Fintype.card V:ℝ)= -2*ε^2/(1/(Fintype.card V:ℝ)):=by field_simp
  simpa only [hc,pow_one,Fintype.card_coe,he] using hh

theorem bernoulli_factor_counts_common_event {T:Type} [Fintype T] [DecidableEq T]
    (c J:ℕ) (hc:2≤c) (S:T→VertexAbsorberTemplate c) (B εv εa εs:ℝ)
    (hB:0≤B) (hεv:0<εv) (hεa:0<εa) (hεs:0<εs) (q:ℕ):
    ∃ N:ℕ,∀ (V C:Type) [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C],
    N≤Fintype.card V→∀ (R:C→Finset V) (w:C→ℝ),
    (∀ i,(R i).card=c)→(∀ Y:Finset V,Fintype.card {i:C // R i=Y}≤J)→
    (∀ i,0≤w i ∧ w i≤B/(Fintype.card V:ℝ)^(c-1))→
    ∀ (s:ℕ),s≤Fintype.card V→∀ (A:Fin s→Finset V)
      (p:ℝ) (hp:0≤p) (hp1:p≤1),
    1-1/(Fintype.card V:ℝ)^q≤
      (FiniteLaw.pi (fun _:V=>FiniteLaw.retentionCoin p hp hp1)).probability
        (fun σ=>
          (∀ v,|resourceRootOmittedLoad R w (fun x=>x∈bernoulliVertexSet σ) v-
            p^(c-1)*hypergraphWeightedDegree R w v|<εv) ∧
          (∀ X:Finset V,X.card=c→
            |absorberGroundCount R S X (bernoulliVertexSet σ)-
              p^(c*c)*Fintype.card (LabelledAbsorberFamily R S X)|<εa*(Fintype.card V:ℝ)^(c*c)) ∧
          (∀ i,|(((A i)∩bernoulliVertexSet σ).card:ℝ)-p*(A i).card|<εs*Fintype.card V)):=by
  let D:ℝ:=((c*c)*Fintype.card T*c^c*J^(2*c+1):ℕ)+1
  have hD:0<D:=by dsimp [D];positivity
  obtain ⟨Nv,hNv⟩:=constant_deviation_failure_eventually_small 1 (((J:ℝ)*B+1)^2) εv
    (by positivity) hεv 1 (q+1)
  obtain ⟨Na,hNa⟩:=constant_deviation_failure_eventually_small 1 (D^2) εa
    (by positivity) hεa c (q+1)
  obtain ⟨Ns,hNs⟩:=constant_deviation_failure_eventually_small 1 1 εs
    (by norm_num) hεs 1 (q+1)
  refine ⟨max 3 (max Nv (max Na Ns)),?_⟩
  intro V C _ _ _ _ hn R w hR hJ hw s hs A p hp hp1
  have hn0:0<Fintype.card V:=by omega
  have hnR:(0:ℝ)<Fintype.card V:=Nat.cast_pos.mpr hn0
  let μ:=FiniteLaw.pi (fun _:V=>FiniteLaw.retentionCoin p hp hp1)
  let bv:=fun (v:V) (σ:V→Bool)=>εv≤|resourceRootOmittedLoad R w (fun x=>x∈bernoulliVertexSet σ) v-
    p^(c-1)*hypergraphWeightedDegree R w v|
  let ba:=fun (X:FixedSubset V c) (σ:V→Bool)=>εa*(Fintype.card V:ℝ)^(c*c)≤
    |absorberGroundCount R S X.val (bernoulliVertexSet σ)-p^(c*c)*Fintype.card (LabelledAbsorberFamily R S X.val)|
  let bs:=fun (i:Fin s) (σ:V→Bool)=>εs*Fintype.card V≤|(((A i)∩bernoulliVertexSet σ).card:ℝ)-p*(A i).card|
  have hv:μ.probability (fun σ=>∃ v,bv v σ)≤1/(Fintype.card V:ℝ)^(q+1):=by
    have hh:μ.probability (fun σ=>∃ v,bv v σ)≤(Fintype.card V:ℝ)*
        (2*Real.exp (-2*εv^2/(((J:ℝ)*B+1)^2/Fintype.card V))):=by
      have hb:=finiteLaw_union_bound μ Finset.univ bv
      simp only [Finset.mem_univ,true_and,exists_const] at hb
      apply hb.trans
      calc
        _≤∑ _:V,2*Real.exp (-2*εv^2/(((J:ℝ)*B+1)^2/Fintype.card V)):=
          Finset.sum_le_sum (fun v _=>bernoulli_root_scaled_tail R c J hc hR hJ w B hB hw hn0 v p hp hp1 εv hεv)
        _=_:=by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    exact hh.trans (hNv (Fintype.card V) (by omega) (Fintype.card V) (Nat.cast_nonneg _)
      (by simp only [pow_one,one_mul];exact le_rfl))
  have ha:μ.probability (fun σ=>∃ X,ba X σ)≤1/(Fintype.card V:ℝ)^(q+1):=by
    have hh:μ.probability (fun σ=>∃ X,ba X σ)≤(Fintype.card (FixedSubset V c):ℝ)*
        (2*Real.exp (-2*εa^2/(D^2/Fintype.card V))):=by
      have hb:=finiteLaw_union_bound μ Finset.univ ba
      simp only [Finset.mem_univ,true_and,exists_const] at hb
      apply hb.trans
      calc
        _≤∑ _:FixedSubset V c,2*Real.exp (-2*εa^2/(D^2/Fintype.card V)):=
          Finset.sum_le_sum (fun X _=>bernoulli_absorber_scaled_tail R S (by omega) X.val X.property J hJ hn0 p hp hp1 εa hεa)
        _=_:=by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    have hcount:(Fintype.card (FixedSubset V c):ℝ)≤(Fintype.card V:ℝ)^c:=by
      have he:Fintype.card (FixedSubset V c)=(Fintype.card V).choose c:=by
        simpa only [Finset.empty_subset,Finset.card_empty,Nat.sub_zero,Fintype.card_subtype_true] using
          fixedSubset_containing_card (V:=V) (∅:Finset V) (by simp : (∅:Finset V).card≤c)
      exact_mod_cast he.le.trans (Nat.choose_le_pow _ _)
    exact hh.trans (hNa (Fintype.card V) (by omega) (Fintype.card (FixedSubset V c))
      (Nat.cast_nonneg _) (by simpa only [one_mul] using hcount))
  have hsz:μ.probability (fun σ=>∃ i,bs i σ)≤1/(Fintype.card V:ℝ)^(q+1):=by
    have hh:μ.probability (fun σ=>∃ i,bs i σ)≤(s:ℝ)*
        (2*Real.exp (-2*εs^2/(1/(Fintype.card V:ℝ)))):=by
      have hb:=finiteLaw_union_bound μ Finset.univ bs
      simp only [Finset.mem_univ,true_and,exists_const] at hb
      apply hb.trans
      calc
        _≤∑ i:Fin s,2*Real.exp (-2*εs^2/(1/(Fintype.card V:ℝ))):=
          Finset.sum_le_sum (fun i _=>bernoulli_domain_size_tail (A i) hn0 p hp hp1 εs hεs)
        _=_:=by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    exact hh.trans (hNs (Fintype.card V) (by omega) s (Nat.cast_nonneg _)
      (by simpa only [one_mul,pow_one] using (Nat.cast_le.mpr hs : (s:ℝ)≤Fintype.card V)))
  let bad:Fin 3→(V→Bool)→Prop:=![fun σ=>∃ v,bv v σ,fun σ=>∃ X,ba X σ,fun σ=>∃ i,bs i σ]
  have hb:∀ i∈(Finset.univ:Finset (Fin 3)),μ.probability (bad i)≤1/(Fintype.card V:ℝ)^(q+1):=by
    intro i _;fin_cases i
    · exact hv
    · exact ha
    · exact hsz
  have hh:=finiteLaw_common_event_lower μ Finset.univ bad (fun _=>1/(Fintype.card V:ℝ)^(q+1)) hb
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Finset.mem_univ,true_implies] at hh
  have hsmall:3*(1/(Fintype.card V:ℝ)^(q+1))≤1/(Fintype.card V:ℝ)^q:=by
    simpa only [mul_one_div] using scaled_inverse_power_le (Fintype.card V) q hn0 3
      (by exact_mod_cast (show 3≤Fintype.card V by omega))
  apply ((sub_le_sub_left hsmall 1).trans hh).trans
  apply finiteLaw_probability_mono
  intro σ hσ
  have hv':¬∃ v,bv v σ:=hσ 0
  have ha':¬∃ X,ba X σ:=hσ 1
  have hs':¬∃ i,bs i σ:=hσ 2
  refine ⟨fun v=>not_le.mp (fun h=>hv' ⟨v,h⟩),?_,fun i=>not_le.mp (fun h=>hs' ⟨i,h⟩)⟩
  intro X hX
  exact not_le.mp (fun h=>ha' ⟨⟨X,hX⟩,h⟩)

end Oberwolfach
