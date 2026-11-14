module

public import Oberwolfach.FreshAlterationScales
public import Oberwolfach.ProfileInducedFactor
public import Oberwolfach.LocalPairRestrictionScales

@[expose] public section

/-! Exact factors after alterations of the sampled vertex set and sparse
pair deletions. All factors are constructed from the original indexed
weights and absorber counts; their existence is not a premise. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I T:Type} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype T] [DecidableEq T]

theorem profile_factor_after_local_changes (a:I→ℕ) (c J:ℕ) (hc:3≤c)
    (ha:∀ i,1≤a i) (hs:∑ i,a i=c) (S:T→VertexAbsorberTemplate c)
    (α b B:ℝ) (hα:0<α) (hb:0<b) (hB:0≤B):
    ∃ η ζ:ℝ,0<η ∧ 0<ζ ∧ ∃ k₀:ℕ,∀ k:ℕ,k₀≤k→
      ∀ (V:I→Type) [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
        (C:Type) [Fintype C] [DecidableEq C],
      ∀ (R:C→Finset (Σ i,V i)) (w:C→ℝ) (A Y:Finset (Σ i,V i)),
      (∀ i,(Finset.univ.filter (fun v:V i=>(⟨i,v⟩:Σ i,V i)∈Y)).card=a i*k)→
      (∀ C₀ i,(Finset.univ.filter (fun v:V i=>(⟨i,v⟩:Σ i,V i)∈R C₀)).card=a i)→
      (∀ U:Finset (Σ i,V i),Fintype.card {C₀:C // R C₀=U}≤J)→
      (∀ C₀,b/(k:ℝ)^(c-1)≤w C₀ ∧ w C₀≤B/(k:ℝ)^(c-1))→
      (A.card:ℝ)≤2*c*k→
      (((A\Y).card+(Y\A).card:ℕ):ℝ)≤ζ*k→
      (∀ v∈Y,|1-resourceRootOmittedLoad R w (fun x=>x∈A) v|≤η)→
      (∀ σ:∀ i,FixedSubset (V i) (a i),profileRootSet σ⊆Y→
        2*α*(k:ℝ)^(c*c)≤absorberGroundCount R S (profileRootSet σ) A)→
      ∀ E:Finset ((Σ i,V i)×(Σ i,V i)),(∀ e∈E,e.1≠e.2)→
      (E.card:ℝ)≤ζ*(k:ℝ)^2→
      (∀ v,((E.filter (fun e=>v=e.1 ∨ v=e.2)).card:ℝ)≤ζ*k)→
      ∃ D:Finset C,((∀ x∈D,∀ y∈D,x≠y→Disjoint (R x) (R y)) ∧ D.biUnion R=Y) ∧
        ∀ C₀∈D,∀ e∈E,¬(e.1∈R C₀ ∧ e.2∈R C₀):=by
  obtain ⟨ηf,hηf,kf,hfactor⟩:=profile_factor_on_subset a c J hc ha hs S α b B hα hb hB
  let Kv:ℝ:=(J:ℝ)*(3*c+1:ℝ)^(c-2)*B
  let Kp:ℝ:=(J:ℝ)*B*((c:ℝ)^(c-2)+(c:ℝ)^(c-3))
  let Ka:ℝ:=((c*c)*Fintype.card T*c^c*J^(2*c+1):ℕ)*(3*c:ℝ)^(c*c-1)
  let Kb:ℝ:=(Fintype.card T:ℝ)*(c:ℝ)^c*(J:ℝ)^(2*c+1)*
    ((c:ℝ)*(c*c:ℕ)*(c:ℝ)^(c*c-1)+((c*c:ℕ):ℝ)^2*(c:ℝ)^(c*c-2))
  have hKv:0≤Kv:=by dsimp [Kv];positivity
  have hKp:0≤Kp:=by dsimp [Kp];positivity
  have hKa:0≤Ka:=by dsimp [Ka];positivity
  have hKb:0≤Kb:=by dsimp [Kb];positivity
  let ζ:=min 1 (min (ηf/(4*(Kv+Kp+1))) (α/(Ka+Kb+1)))
  have hζ:0<ζ:=by dsimp [ζ];positivity
  have hζload:ζ*(Kv+Kp)≤ηf/2:=by
    have hh:ζ≤ηf/(4*(Kv+Kp+1)):=
      (min_le_right _ _).trans (min_le_left _ _)
    have ht:=(le_div_iff₀ (by positivity : (0:ℝ)<4*(Kv+Kp+1))).mp hh
    nlinarith only [ht,hζ,hηf]
  have hζabs:ζ*(Ka+Kb)≤α:=by
    have hh:ζ≤α/(Ka+Kb+1):=(min_le_right _ _).trans (min_le_right _ _)
    have ht:=(le_div_iff₀ (by positivity : (0:ℝ)<Ka+Kb+1)).mp hh
    nlinarith only [ht,hζ]
  refine ⟨ηf/2,ζ,by positivity,hζ,max 1 kf,?_⟩
  intro k hk V _ _ C _ _ R w A Y hY hR hJ hw hA hchange herr habs E hE hEsize hEd
  have hk1:1≤k:=by omega
  have hkR:(1:ℝ)≤k:=by exact_mod_cast hk1
  have hkp:(0:ℝ)<k:=by exact_mod_cast (show 0<k by omega)
  have hYcard:Y.card=c*k:=by rw [sigma_finset_card];simp only [hY,←Finset.sum_mul,hs]
  have hYsize:(Y.card:ℝ)=(c:ℝ)*k:=by exact_mod_cast hYcard
  have hU:((A∪Y).card:ℝ)≤3*c*k:=by
    have hh:((A∪Y).card:ℝ)≤(A.card:ℝ)+Y.card:=by exact_mod_cast Finset.card_union_le A Y
    rw [hYsize] at hh
    linarith
  have hU1:((A∪Y).card:ℝ)+1≤(3*c+1:ℝ)*k:=by nlinarith only [hU,hkR]
  have hRC (C₀:C):(R C₀).card=c:=by rw [sigma_finset_card];simp only [hR];exact hs
  have hw' (C₀:C):0≤w C₀ ∧ w C₀≤B/(k:ℝ)^(c-1):=
    ⟨(by positivity : (0:ℝ)≤b/(k:ℝ)^(c-1)).trans (hw C₀).1,(hw C₀).2⟩
  let P:=fun C₀=>∀ e:E,¬(e.val.1∈R C₀ ∧ e.val.2∈R C₀)
  let R':=candidateResourceSet R P
  let w':=fun D:{C₀:C // P C₀}=>w D.val
  have herr' (v:Σ i,V i) (hv:v∈Y):
      |1-hypergraphWeightedDegree R' (inducedResourceWeight R' w' Y) v|≤ηf:=by
    have hvchange:=root_omitted_local_change_scale R c J (by omega) hRC hJ w B k (3*c+1) ζ
      hB hkp (by positivity) hζ.le hw' A Y v hchange hU1
    rw [root_omitted_load_induced R w Y v,Finset.insert_eq_of_mem hv] at hvchange
    have hvbound:|resourceRootOmittedLoad R w (fun x=>x∈A) v-
        hypergraphWeightedDegree R (inducedResourceWeight R w Y) v|≤ζ*Kv:=by
      convert hvchange using 1 <;> dsimp [Kv] <;> ring
    obtain ⟨hp0,hp1⟩:=resource_sparse_pairs_degree_loss_scale R c J hc hRC hJ w B k c ζ
      hB hkp (Nat.cast_nonneg c) hζ.le hw' Y hYsize.le E hE v (hEd v) hEsize
    have hpbound:hypergraphWeightedDegree R (inducedResourceWeight R w Y) v-
        hypergraphWeightedDegree R (pairRestrictedResourceWeight R (inducedResourceWeight R w Y) E) v≤ζ*Kp:=by
      convert hp1 using 1 <;> dsimp [Kp] <;> ring
    rw [candidate_resource_induced_pair_degree]
    apply abs_le.mpr
    have h₁:=abs_le.mp (herr v hv)
    have h₂:=abs_le.mp hvbound
    constructor <;> nlinarith only [h₁.1,h₁.2,h₂.1,h₂.2,hp0,hpbound,hζload]
  have habs' (σ:∀ i,FixedSubset (V i) (a i)) (hσ:profileRootSet σ⊆Y):
      α*(k:ℝ)^(c*c)≤absorberGroundCount R' S (profileRootSet σ) Y:=by
    have hX:(profileRootSet σ).card=c:=(profileRootSet_card σ).trans hs
    have hvchange:=absorber_ground_change_scale R S (by omega) (profileRootSet σ) A Y hX J hJ
      k (3*c) ζ hkp.le (by positivity) hζ.le hchange hU
    have hvbound:|absorberGroundCount R S (profileRootSet σ) A-
        absorberGroundCount R S (profileRootSet σ) Y|≤ζ*Ka*(k:ℝ)^(c*c):=by
      convert hvchange using 1 <;> dsimp [Ka] <;> ring
    have hpair:=absorber_ground_sparse_pairs_scale R S (by omega) (profileRootSet σ) Y hX J hJ E hE
      k c ζ hkp.le (Nat.cast_nonneg c) hζ.le hYsize.le (fun v _=>hEd v) hEsize
    have hpbound:absorberGroundCount R S (profileRootSet σ) Y≤
        absorberGroundCount R' S (profileRootSet σ) Y+ζ*Kb*(k:ℝ)^(c*c):=by
      convert hpair using 1 <;> dsimp [Kb] <;> ring
    have hsum:=mul_le_mul_of_nonneg_right hζabs (pow_nonneg hkp.le (c*c))
    have hvhi:=(abs_le.mp hvbound).2
    have hh:=habs σ hσ
    nlinarith only [hh,hvhi,hpbound,hsum]
  have hf:=hfactor k (by omega) V {C₀:C // P C₀} R' w' Y hY
    (fun D i=>hR D.val i) (candidate_resource_multiplicity R P J hJ) (fun D=>hw D.val) herr' habs'
  obtain ⟨D,hD,havoid⟩:=candidate_resource_decomposition_lift R P Y hf
  refine ⟨D,hD,?_⟩
  intro C₀ hC e he
  exact havoid C₀ hC ⟨e,he⟩

end Oberwolfach
