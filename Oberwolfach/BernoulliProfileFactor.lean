module

public import Oberwolfach.BernoulliFactorCommonEvent
public import Oberwolfach.ProfileFactorAfterChanges
public import Oberwolfach.FreshFactorScaleComparison

@[expose] public section

/-! Factor extraction on one independent vertex-retention event, uniformly
for every later small alteration and sparse pair deletion. The tolerances
precede the retention probability; only the order threshold depends on it. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I T:Type} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype T] [DecidableEq T]

theorem bernoulli_profile_factor_common_event (a:I→ℕ) (c J:ℕ) (hc:3≤c)
    (ha:∀ i,1≤a i) (hs:∑ i,a i=c) (S:T→VertexAbsorberTemplate c)
    (α b B:ℝ) (hα:0<α) (hb:0<b) (hB:0≤B):
    ∃ η ζ:ℝ,0<η ∧ 0<ζ ∧ ∀ (p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ),∃ N:ℕ,
      ∀ (V:I→Type) [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
        (C:Type) [Fintype C] [DecidableEq C],
      N≤Fintype.card (Σ i,V i)→∀ (R:C→Finset (Σ i,V i)) (w:C→ℝ),
      (∀ C₀ i,(Finset.univ.filter (fun v:V i=>(⟨i,v⟩:Σ i,V i)∈R C₀)).card=a i)→
      (∀ U:Finset (Σ i,V i),Fintype.card {C₀:C // R C₀=U}≤J)→
      (∀ C₀,b/(Fintype.card (Σ i,V i):ℝ)^(c-1)≤w C₀ ∧
        w C₀≤B/(Fintype.card (Σ i,V i):ℝ)^(c-1))→
      (∀ v,|1-hypergraphWeightedDegree R w v|≤η)→
      (∀ σ:∀ i,FixedSubset (V i) (a i),
        α*(Fintype.card (Σ i,V i):ℝ)^(c*c)≤Fintype.card (LabelledAbsorberFamily R S (profileRootSet σ)))→
      1-1/(Fintype.card (Σ i,V i):ℝ)^q≤
        (FiniteLaw.pi (fun _:Σ i,V i=>FiniteLaw.retentionCoin p hp.le hp1)).probability
          (fun σ=> |((bernoulliVertexSet σ).card:ℝ)-p*Fintype.card (Σ i,V i)|≤
            p*Fintype.card (Σ i,V i)/4 ∧
            ∀ (Y:Finset (Σ i,V i)) (k:ℕ),
            (∀ i,(Finset.univ.filter (fun v:V i=>(⟨i,v⟩:Σ i,V i)∈Y)).card=a i*k)→
            (((bernoulliVertexSet σ\Y).card+(Y\bernoulliVertexSet σ).card:ℕ):ℝ)≤
              ζ*(p*Fintype.card (Σ i,V i))→
            ∀ E:Finset ((Σ i,V i)×(Σ i,V i)),(∀ e∈E,e.1≠e.2)→
            (E.card:ℝ)≤ζ*(p*Fintype.card (Σ i,V i))^2→
            (∀ v,((E.filter (fun e=>v=e.1 ∨ v=e.2)).card:ℝ)≤ζ*(p*Fintype.card (Σ i,V i)))→
            ∃ D:Finset C,((∀ x∈D,∀ y∈D,x≠y→Disjoint (R x) (R y)) ∧ D.biUnion R=Y) ∧
              ∀ C₀∈D,∀ e∈E,¬(e.1∈R C₀ ∧ e.2∈R C₀)):=by
  let M:ℝ:=2*c
  have hcR:(1:ℝ)≤c:=by exact_mod_cast (show 1≤c by omega)
  have hM:0<M:=by dsimp [M];positivity
  have hM1:1≤M:=by dsimp [M];linarith
  let αf:=α/(4*(2:ℝ)^(c*c))
  let bf:=b/M^(c-1)
  let Bf:=(2:ℝ)^(c-1)*B
  obtain ⟨ηf,ζf,hηf,hζf,kf,hfactor⟩:=profile_factor_after_local_changes a c J hc ha hs S αf bf Bf
    (by dsimp [αf];positivity) (by dsimp [bf];positivity) (by dsimp [Bf];positivity)
  let ζ:=min (1/4:ℝ) (min (ζf/M^2) (1/M^2))
  have hζ:0<ζ:=by dsimp [ζ];positivity
  have hζ4:ζ≤1/4:=min_le_left _ _
  have hζM2:ζ*M^2≤ζf:=by
    have hh:ζ≤ζf/M^2:=(min_le_right _ _).trans (min_le_left _ _)
    exact (le_div_iff₀ (sq_pos_of_pos hM)).mp hh
  have hζM21:ζ*M^2≤1:=by
    have hh:ζ≤1/M^2:=(min_le_right _ _).trans (min_le_right _ _)
    exact (le_div_iff₀ (sq_pos_of_pos hM)).mp hh
  have hζM:ζ*M≤ζf:=by
    have hh:=mul_le_mul_of_nonneg_left (show M≤M^2 by nlinarith only [hM1]) hζ.le
    exact hh.trans hζM2
  have hζM1:ζ*M≤1:=by
    have hh:=mul_le_mul_of_nonneg_left (show M≤M^2 by nlinarith only [hM1]) hζ.le
    exact hh.trans hζM21
  refine ⟨ηf/2,ζ,by positivity,hζ,?_⟩
  intro p hp hp1 q
  obtain ⟨Ne,hNe⟩:=bernoulli_factor_counts_common_event c J (by omega) S B
    ((ηf/2)*p^(c-1)) ((α/2)*p^(c*c)) (p/4) hB (by positivity) (by positivity) (by positivity) q
  obtain ⟨Nb,hNb⟩:=exists_nat_ge (M*kf/p)
  refine ⟨max 1 (max Ne Nb),?_⟩
  intro V _ _ C _ _ hn R w hR hJ hw herr habs
  let n:ℝ:=Fintype.card (Σ i,V i)
  have hnpos:0<n:=by dsimp [n];exact_mod_cast (show 0<Fintype.card (Σ i,V i) by omega)
  have hRC (C₀:C):(R C₀).card=c:=by rw [sigma_finset_card];simp only [hR];exact hs
  have hw0 (C₀:C):0≤w C₀:=(by positivity : (0:ℝ)≤b/n^(c-1)).trans (hw C₀).1
  have hevent:=hNe (Σ i,V i) C (by omega) R w hRC hJ
    (fun C₀=>⟨hw0 C₀,(hw C₀).2⟩) 1 (by omega) (fun _=>Finset.univ) p hp.le hp1
  apply hevent.trans
  apply finiteLaw_probability_mono
  intro σ hσ
  refine ⟨?_,?_⟩
  · have hh:=(hσ.2.2 0).le
    simp only [Finset.univ_inter,Finset.card_univ] at hh
    convert hh using 1 <;> ring
  · intro Y k hY hchange E hE hEsize hEd
    let A:=bernoulliVertexSet σ
    let s:=p*n
    have hsp:0<s:=mul_pos hp hnpos
    have hYcard:Y.card=c*k:=by rw [sigma_finset_card];simp only [hY,←Finset.sum_mul,hs]
    have hAc:|(A.card:ℝ)-s|≤s/4:=by
      have hh:=(hσ.2.2 0).le
      simp only [Finset.univ_inter,Finset.card_univ] at hh
      convert hh using 1 <;> dsimp [A,s,n] <;> ring
    obtain ⟨hsk,hks,hkp⟩:=altered_profile_scale_bounds c (by omega) A Y k s ζ hsp hζ.le hζ4 hAc hchange hYcard
    change s≤M*k at hsk
    have hk:kf≤k:=by
      have hN:(Nb:ℝ)≤n:=by dsimp [n];exact_mod_cast (show Nb≤Fintype.card (Σ i,V i) by omega)
      have hh:=(div_le_iff₀ hp).mp (hNb.trans hN)
      have hkR:(kf:ℝ)≤k:=by dsimp [s] at hsk;nlinarith only [hh,hsk,hM]
      exact_mod_cast hkR
    have hΔ:(((A\Y).card+(Y\A).card:ℕ):ℝ)≤ζf*k:=by
      calc
        _≤ζ*s:=hchange
        _≤ζ*(M*k):=mul_le_mul_of_nonneg_left hsk hζ.le
        _≤ζf*k:=by nlinarith only [mul_le_mul_of_nonneg_right hζM hkp.le]
    have hΔ1:(((A\Y).card+(Y\A).card:ℕ):ℝ)≤(k:ℝ):=by
      calc
        _≤ζ*s:=hchange
        _≤ζ*(M*k):=mul_le_mul_of_nonneg_left hsk hζ.le
        _≤k:=by nlinarith only [mul_le_mul_of_nonneg_right hζM1 hkp.le]
    have hA:(A.card:ℝ)≤2*c*k:=by
      have hh:(A.card:ℝ)≤(Y.card:ℝ)+((A\Y).card:ℝ):=by
        have ht:A.card≤Y.card+(A\Y).card:=by
          simpa only [Nat.add_comm] using (Finset.card_le_card_sdiff_add_card (s:=A) (t:=Y))
        exact_mod_cast ht
      have hYc:(Y.card:ℝ)=(c:ℝ)*k:=by exact_mod_cast hYcard
      have hd:((A\Y).card:ℝ)≤((A\Y).card+(Y\A).card:ℕ):=by exact_mod_cast Nat.le_add_right (A\Y).card (Y\A).card
      rw [hYc] at hh
      nlinarith only [hh,hd,hΔ1,mul_le_mul_of_nonneg_right hcR hkp.le]
    let w':C→ℝ:=fun C₀=>w C₀/p^(c-1)
    have hw' (C₀:C):bf/(k:ℝ)^(c-1)≤w' C₀ ∧ w' C₀≤Bf/(k:ℝ)^(c-1):=by
      have hws:b/s^(c-1)≤w' C₀ ∧ w' C₀≤B/s^(c-1):=by
        constructor
        · have hh:=div_le_div_of_nonneg_right (hw C₀).1 (pow_nonneg hp.le (c-1))
          convert hh using 1 <;> dsimp [s,w',n] <;> rw [mul_pow] <;> field_simp
        · have hh:=div_le_div_of_nonneg_right (hw C₀).2 (pow_nonneg hp.le (c-1))
          convert hh using 1 <;> dsimp [s,w',n] <;> rw [mul_pow] <;> field_simp
      exact fresh_weight_scale_bounds (c-1) c k s b B (w' C₀) (by positivity) hkp hsp hb.le hB hsk hks hws
    have herr' (v:Σ i,V i) (_hv:v∈Y):
        |1-resourceRootOmittedLoad R w' (fun x=>x∈A) v|≤ηf:=by
      rw [resourceRootOmittedLoad_div]
      have hh:=omitted_load_rescaling_error
        (resourceRootOmittedLoad R w (fun x=>x∈A) v) (hypergraphWeightedDegree R w v)
        (p^(c-1)) (ηf/2) (ηf/2) (pow_pos hp _) (hσ.1 v).le (herr v)
      convert hh using 1 <;> ring
    have habs' (ρ:∀ i,FixedSubset (V i) (a i)) (_hρ:profileRootSet ρ⊆Y):
        2*αf*(k:ℝ)^(c*c)≤absorberGroundCount R S (profileRootSet ρ) A:=by
      have hX:(profileRootSet ρ).card=c:=(profileRootSet_card ρ).trans hs
      have hh:=(abs_le.mp (hσ.2.1 (profileRootSet ρ) hX).le).1
      have hl:=mul_le_mul_of_nonneg_left (habs ρ) (pow_nonneg hp.le (c*c))
      have hlow:(α/2)*s^(c*c)≤absorberGroundCount R S (profileRootSet ρ) A:=by
        dsimp [s]
        rw [mul_pow]
        nlinarith only [hh,hl]
      apply le_trans _ hlow
      calc
        _≤2*αf*(2*s)^(c*c):=mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hkp.le hks _) (by dsimp [αf];positivity)
        _=(α/2)*s^(c*c):=by dsimp [αf];rw [mul_pow];field_simp;norm_num
    have hEs:(E.card:ℝ)≤ζf*(k:ℝ)^2:=by
      calc
        _≤ζ*s^2:=hEsize
        _≤ζ*(M*k)^2:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsp.le hsk 2) hζ.le
        _≤ζf*(k:ℝ)^2:=by nlinarith only [mul_le_mul_of_nonneg_right hζM2 (sq_nonneg (k:ℝ))]
    have hEd' (v:Σ i,V i):((E.filter (fun e=>v=e.1 ∨ v=e.2)).card:ℝ)≤ζf*k:=by
      calc
        _≤ζ*s:=hEd v
        _≤ζ*(M*k):=mul_le_mul_of_nonneg_left hsk hζ.le
        _≤ζf*k:=by nlinarith only [mul_le_mul_of_nonneg_right hζM hkp.le]
    exact hfactor k hk V C R w' A Y hY hR hJ hw' hA hΔ herr' habs' E hE hEs hEd'

end Oberwolfach
