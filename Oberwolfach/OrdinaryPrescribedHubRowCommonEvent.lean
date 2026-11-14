module

public import Oberwolfach.OrdinaryHubAndRowCommonEvent
public import Oberwolfach.PrescribedPackingCommonEvent
public import Oberwolfach.PrescribedCoverRootInputs
public import Oberwolfach.WheelFamilyDeletionChanges
public import Oberwolfach.HubRowPackingUnion
public import Oberwolfach.HubRowPackingSupport
public import Oberwolfach.DeepCoverInnerIntersection
public import Oberwolfach.PrescribedDeepPackingUnion

@[expose] public section

/-! One event for the prescribed-inner-edge packing followed by the actual
hub and row covers in its remainder. All later choices share the original
law. The hub counting domain is fixed before sampling. Only the designated
root balances and congruences are assumed of the comparison host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 15000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_prescribed_hub_row_common_event (m:ℕ) (hm:3≤m) (α p ω:ℝ)
    (hα:0<α) (hp:0<p) (hp1:p≤1) (hω:0<ω):
    ∃ K:ℕ,0<K ∧ ∃ a ε₀ ρ θ:ℝ,0<a ∧ 0<ε₀ ∧ 0<ρ ∧ 0<θ ∧
    ∀ Dmax d q₀:ℕ,∀ hd:2≤d,∃ N:ℕ,
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    ∀ (P F:SimpleGraph V) (π:Equiv.Perm V) (J:Finset U),N≤Fintype.card V →
      (J.card:ℝ)≤a*Fintype.card V →
      ω*Fintype.card V≤((Finset.univ\J).card:ℝ) → Fintype.card U≤Fintype.card V →
      (∀ v,(cycleThreshold (m+1)+α)*Fintype.card V≤(P.degree v:ℝ)) →
      (∀ v,F.degree v≤Dmax) → permutationConflictGraph π (3*d)≤F →
      (∀ z l,0<l→l<2*d+1→(π^l) z≠z) →
    ∀ (pR pH D ε:ℝ) (hpR:p≤pR) (hpR1:pR≤1),p≤pH → pH≤1 →
      (Fintype.card V:ℝ)/2≤D → 0≤ε → ε≤ε₀ →
      (∀ v,|(P.degree v:ℝ)-D|≤ε*Fintype.card V) → pR*D=2*Fintype.card U*pH →
    ∀ (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (j:Color),(∀ u,s u j=pH) →
    1-1/(Fintype.card V:ℝ)^q₀≤
      (FiniteLaw.pi (rawWheelLaw (fun _=>pR) (fun _=>hp.le.trans hpR) (fun _=>hpR1) d hd q hq hQ s hs hS)).probability
      (fun σ=>∀ (Q:SimpleGraph V) (H:V→U→Prop) (L:ℝ),Q≤P → 0≤L → L≤ρ*Fintype.card V →
        (∀ v,(F.degree v:ℝ)≤L) →
        (∀ v,((changed ((rawWheelGraph P σ).neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L) →
        (∀ v,((changed (Finset.univ.filter (rawWheelSpokes π d σ j v)) (Finset.univ.filter (H v))).card:ℝ)≤L) →
        (∀ u,((changed (Finset.univ.filter (fun v=>rawWheelSpokes π d σ j v u))
          (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤L) →
      ∀ I:Finset V,(I.card:ℝ)≤a*Fintype.card V →
      ∀ (Nr Ns D₀:ℕ) (v w:Fin Nr→V),
        (∀ i,v i∈I) → (∀ i,w i∈I) → (∀ i,Q.Adj (v i) (w i)) → (∀ i,¬F.Adj (v i) (w i)) →
        (∀ i j,i≠j→¬((v i=v j∧w i=w j)∨(v i=w j∧w i=v j))) →
        (∀ b,(Finset.univ.filter (fun i=>b=v i∨b=w i)).card≤D₀) →
      ∀ (z:Fin Ns→V) (b:Fin Ns→U), (∀ i,z i∈I) → (∀ i,b i∈J) → (∀ i,H (z i) (b i)) →
        Function.Injective (fun i=>(z i,b i)) →
        (∀ t,(Finset.univ.filter (fun i=>t=z i)).card≤D₀) →
        (∀ t,(Finset.univ.filter (fun i=>b i=t)).card≤D₀) →
        ((Nr+Ns:ℕ):ℝ)≤a^2*(Fintype.card V:ℝ)^2 → (D₀:ℝ)≤a*Fintype.card V →
      let e:(Fin Nr⊕Fin Ns)→Sym2 V⊕(V×U):=Sum.elim (fun i=>Sum.inl s(v i,w i)) (fun i=>Sum.inr (z i,b i))
      let E₀:=Finset.univ.image e
      ∀ (nh:ℕ) (u:Fin nh→U),Function.Injective u → (2*nh:ℝ)≤L → (∀ i,u i∈J) →
        (∀ i,(m+1)∣(Finset.univ.filter (fun t=>H t (u i))).card) →
      ∀ (nr:ℕ) (x:Fin nr→V),(nr:ℝ)≤θ*Fintype.card V → Function.Injective x → (∀ i,x i∈I) →
        (∀ i t,Q.Adj (x i) t→¬F.Adj (x i) t) →
        (∀ i,Q.degree (x i)=2*(Finset.univ.filter (H (x i))).card) →
        (∀ i t,t∈I→Q.Adj (x i) t→Sum.inl s(x i,t)∈E₀) →
        (∀ i t,t∈J→H (x i) t→Sum.inr (x i,t)∈E₀) →
        (∀ i t,t∈I→H t (u i)→Sum.inr (t,u i)∈E₀) →
      ∃ C:(Fin Nr⊕Fin Ns)→OrdinaryWheel Q F H (m+1),
        (∀ i j,i≠j→Disjoint (ordinaryWheelResources (C i)) (ordinaryWheelResources (C j))) ∧
        (∀ i,ordinaryWheelResources (C i)∩ordinaryHostResources (spanningRestriction Q I)
          (fun t a=>H t a∧t∈I∧a∈J)={e i}) ∧
        (∀ t,((wheelFamilyRim C).degree t:ℝ)≤12*a*Fintype.card V) ∧
        (∀ t,((Finset.univ.filter (wheelFamilySpokes C t)).card:ℝ)≤6*a*Fintype.card V) ∧
        (∀ t,((Finset.univ.filter (fun v=>wheelFamilySpokes C v t)).card:ℝ)≤3*a*Fintype.card V*(m+1)) ∧
        ∃ M:Finset (OrdinaryWheel (Q\wheelFamilyRim C) F
          (fun v t=>H v t∧¬wheelFamilySpokes C v t) (m+1)),
          (∀ A∈M,∀ B∈M,A≠B→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B)) ∧
          (∀ i t,(ordinaryWheelRimGraph M).Adj (x i) t↔(Q\wheelFamilyRim C).Adj (x i) t) ∧
          (∀ i t,ordinaryPackingSpokes M (x i) t↔H (x i) t∧¬wheelFamilySpokes C (x i) t) ∧
          (∀ i t,ordinaryPackingSpokes M t (u i)↔H t (u i)∧¬wheelFamilySpokes C t (u i)) ∧
          (∀ t∉I,(ordinaryWheelRimGraph M).degree t≤2*nh+nr*(2*(K+1))) ∧
          (∀ t∉I,(Finset.univ.filter (ordinaryPackingSpokes M t)).card≤nh+nr*(K+1)) ∧
          (∀ t∉J,(Finset.univ.filter (fun v=>ordinaryPackingSpokes M v t)).card≤nr*(m+1)) ∧
          (∀ W∈M,
            (∃ i,ordinaryWheelHub W=u i ∧ ∀ v∈(ordinaryWheelRim W).support,v∉I) ∨
            (∃ i,x i∈(ordinaryWheelRim W).support ∧ ordinaryWheelHub W∉J ∧
              ∀ v∈(ordinaryWheelRim W).support,v=x i∨v∉I)) ∧
          ∃ P':Finset (OrdinaryWheel Q F H (m+1)),
            (∀ A∈P',∀ B∈P',A≠B→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B)) ∧
            P'.biUnion ordinaryWheelResources∩ordinaryHostResources (spanningRestriction Q I)
              (fun v a=>H v a∧v∈I∧a∈J)=E₀ ∧
            (∀ i v,(ordinaryWheelRimGraph P').Adj (x i) v↔Q.Adj (x i) v) ∧
            (∀ i v,ordinaryPackingSpokes P' (x i) v↔H (x i) v) ∧
            (∀ i v,ordinaryPackingSpokes P' v (u i)↔H v (u i))):=by
  obtain ⟨K,hK,ε₀,ρ₀,θ,hε₀,hρ₀,hθ,hdeep⟩:=ordinary_hub_and_row_common_event m hm α p ω hα hp hp1 hω
  let γ:=min α 1
  have hγ:0<γ:=lt_min hα zero_lt_one
  obtain ⟨a₀,ha₀,ha₀1,hpre⟩:=prescribed_inner_packing_common_event (m+1) (by omega) p γ ω 1 hp hp1 hγ (min_le_right _ _) hω le_rfl
  let c:ℝ:=12+3*(m+1)
  have hc:0<c:=by dsimp [c];positivity
  let a:=min a₀ (min (ρ₀/(4*c)) (p^6*γ*(min 1 ω)/8))
  let ρ:=min (ρ₀/4) (p^6*γ*(min 1 ω)/48)
  have ha:0<a:=lt_min ha₀ (lt_min (by positivity) (by positivity))
  have hρ:0<ρ:=lt_min (by positivity) (by positivity)
  have ha₀':a≤a₀:=min_le_left _ _
  have haC:4*c*a≤ρ₀:=by
    have hh: a≤ρ₀/(4*c):=(min_le_right _ _).trans (min_le_left _ _)
    have ht: a*(4*c)≤ρ₀:=(le_div_iff₀ (by positivity)).mp hh
    nlinarith only [ht]
  have haScale:8*a≤p^6*γ*min 1 ω:=by
    have hh:a≤p^6*γ*(min 1 ω)/8:=(min_le_right _ _).trans (min_le_right _ _)
    linarith only [hh]
  have hρ₀':4*ρ≤ρ₀:=by have hh:=min_le_left (ρ₀/4) (p^6*γ*(min 1 ω)/48);dsimp [ρ];linarith only [hh]
  have hρScale:48*ρ≤p^6*γ*min 1 ω:=by
    have hh:=min_le_right (ρ₀/4) (p^6*γ*(min 1 ω)/48);dsimp [ρ];linarith only [hh]
  refine ⟨K,hK,a,ε₀,ρ,θ,ha,hε₀,hρ,hθ,?_⟩
  intro Dmax d q₀ hd
  obtain ⟨Nd,hd'⟩:=hdeep Dmax d (q₀+1) hd
  obtain ⟨Np,hp'⟩:=hpre a Dmax ha ha₀' (Nat.cast_nonneg _) d (q₀+1) hd
  refine ⟨max 2 (max Nd Np),?_⟩
  intro V U Γ Color _ _ _ _ _ _ P F π J hn hJ hB hU hP hF hclose hnoshort
    pR pH D ε hpR hpR1 hpH hpH1 hD hε hεsmall hreg hbalance q hq hQ s hs hS j hj
  have hnN:0<Fintype.card V:=by omega
  have hnR:(0:ℝ)<Fintype.card V:=Nat.cast_pos.mpr hnN
  have hUlo:ω*Fintype.card V≤(Fintype.card U:ℝ):=hB.trans (Nat.cast_le.mpr (Finset.card_le_univ _))
  have hPpre (v:V):(1/2+γ)*(Finset.univ:Finset V).card≤((Finset.univ∩P.neighborFinset v).card:ℝ):=by
    have hh:(1/2:ℝ)+γ≤cycleThreshold (m+1)+α:=by
      have hhalf:=cycleThreshold_half_le (show 3≤m+1 by omega)
      have hga:=min_le_left α 1
      dsimp [γ];linarith only [hhalf,hga]
    simpa only [Finset.card_univ,Finset.univ_inter,SimpleGraph.card_neighborFinset_eq_degree] using
      (mul_le_mul_of_nonneg_right hh hnR.le).trans (hP v)
  have pd:=hd' V U Γ Color P F π (Finset.univ\J) (by omega) hB hU hP hF hclose hnoshort
    pR pH D ε hpR hpR1 hpH hpH1 hD hε hεsmall hreg hbalance q hq hQ s hs hS j hj
  have pp:=hp' V U Γ Color P F π Finset.univ Finset.univ (by simpa using (show Np≤Fintype.card V by omega))
    (by simp) (by simpa using (Nat.cast_le.mpr hU:(Fintype.card U:ℝ)≤Fintype.card V))
    (by simpa using hUlo) hclose (fun v=>Nat.cast_le.mpr (hF v)) hPpre hnoshort
    pR pH (hp.le.trans hpR) hpR1 hpR hpH q hq hQ s hs hS j hj
  let μ:=FiniteLaw.pi (rawWheelLaw (fun _:Sym2 V=>pR) (fun _=>hp.le.trans hpR) (fun _=>hpR1) d hd q hq hQ s hs hS)
  have combine (E F:((e:RawWheelCoordinate V U)→RawWheelCoordinateState Γ Color e)→Prop)
      (he:1-1/(Fintype.card V:ℝ)^(q₀+1)≤μ.probability E)
      (hf:1-1/(Fintype.card V:ℝ)^(q₀+1)≤μ.probability F):
      1-1/(Fintype.card V:ℝ)^q₀≤μ.probability (fun σ=>E σ∧F σ):=by
    have hi:=finiteLaw_good_intersection μ E F (1/(Fintype.card V:ℝ)^(q₀+1)) hf
    have hb:=scaled_inverse_power_le (Fintype.card V) q₀ hnN 2 (by exact_mod_cast (show 2≤Fintype.card V by omega))
    have hb':2*(1/(Fintype.card V:ℝ)^(q₀+1))≤1/(Fintype.card V:ℝ)^q₀:=by convert hb using 1 <;> ring
    linarith only [he,hi,hb']
  have joint:=combine _ _ (by simpa only [Finset.card_univ] using pp) pd
  apply joint.trans
  apply finiteLaw_probability_mono
  intro σ hσ Q H L hQP hL hLρ hFL hQR hHr hHc I hI Nr Ns D₀ v w hv hw hvw hFvw hedge hend
    z b hz hb hH hspoke hsend hshub hN hD₀
  dsimp only
  intro nh u hu hnh huJ hdiv nr x hnr hx hxI hFx hbal hrim hrow hcol
  let X:=Finset.univ\I
  let B:=Finset.univ\J
  have hsmallV:8*a≤p^6*γ:=by
    have hh:=mul_le_mul_of_nonneg_left (min_le_left 1 ω) (show 0≤p^6*γ by positivity)
    nlinarith only [haScale,hh]
  have hsmallU:8*a*Fintype.card V≤p^6*γ*Fintype.card U:=by
    have hh:=mul_le_mul_of_nonneg_left (min_le_right 1 ω) (show 0≤p^6*γ by positivity)
    have ht:=mul_le_mul_of_nonneg_left hUlo (show 0≤p^6*γ by positivity)
    have hs:=mul_le_mul_of_nonneg_right (haScale.trans hh) hnR.le
    nlinarith only [hs,ht]
  have hchangeV:6*L≤(p^6*γ/4)*(Finset.univ:Finset V).card:=by
    have hh:=mul_le_mul_of_nonneg_left (min_le_left 1 ω) (show 0≤p^6*γ by positivity)
    simp only [Finset.card_univ]
    have hs:=mul_le_mul_of_nonneg_right (hρScale.trans hh) hnR.le
    nlinarith only [hs,hLρ,hL]
  have hchangeU:6*L≤(p^6*γ/4)*(Finset.univ:Finset U).card:=by
    have hh:=mul_le_mul_of_nonneg_left (min_le_right 1 ω) (show 0≤p^6*γ by positivity)
    have ht:=mul_le_mul_of_nonneg_left hUlo (show 0≤p^6*γ by positivity)
    simp only [Finset.card_univ]
    have hs:=mul_le_mul_of_nonneg_right (hρScale.trans hh) hnR.le
    nlinarith only [hs,hLρ,ht,hL]
  have hXloss:((Finset.univ\X).card:ℝ)≤p^6*γ*(Finset.univ:Finset V).card/8:=by
    have he:Finset.univ\X=I:=by ext t;simp [X]
    rw [he,Finset.card_univ]
    have hs:=mul_le_mul_of_nonneg_right hsmallV hnR.le
    nlinarith only [hI,hs]
  have hBloss:((Finset.univ\B).card:ℝ)≤p^6*γ*(Finset.univ:Finset U).card/8:=by
    have he:Finset.univ\B=J:=by ext t;simp [B]
    rw [he,Finset.card_univ]
    nlinarith only [hJ,hsmallU]
  obtain ⟨C,hC,hinner,hdeg,hCr,hCc⟩:=hσ.1 Q H L hL hchangeV hchangeU
    (fun t=>by simpa only [Finset.univ_inter] using hQR t)
    (fun t=>by simpa only [Finset.univ_inter] using hHr t)
    (fun t _=>by simpa only [Finset.univ_inter] using hHc t)
    I X J B (by apply Finset.disjoint_left.mpr; intro t ht hh; exact (Finset.mem_sdiff.mp hh).2 ht)
    (by apply Finset.disjoint_left.mpr; intro t ht hh; exact (Finset.mem_sdiff.mp hh).2 ht)
    Nr Ns D₀ v w hv hw hvw hFvw hedge hend z b hz hb hH hspoke hsend hshub (Finset.subset_univ _)
    (by simpa only [Finset.card_univ] using hN) (by simpa only [Finset.card_univ] using hD₀) hXloss hBloss
  let e:(Fin Nr⊕Fin Ns)→Sym2 V⊕(V×U):=Sum.elim (fun i=>Sum.inl s(v i,w i)) (fun i=>Sum.inr (z i,b i))
  have hcovered:Finset.univ.image e⊆ordinaryHostResources (wheelFamilyRim C) (wheelFamilySpokes C):=by
    have hh:=(prescribed_wheel_family_exact_union C _ e hC hinner).2.1
    rw [←hh];exact Finset.inter_subset_left
  have hgeo:=prescribed_cover_root_geometry C I J (Finset.univ.image x) (Finset.univ.image u) (Finset.univ.image e) hcovered
    (by intro t ht y hy hty;obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp ht;exact hrim i y hy hty)
    (by intro t ht y hy hty;obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp ht;exact hrow i y hy hty)
    (by intro t ht y hy hyt;obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp ht;exact hcol i y hy hyt)
  have hbalance':=prescribed_wheel_family_root_balance C hC (Finset.univ.image x) (Finset.univ.image u)
    (by intro t ht;obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp ht;exact hbal i)
    (by intro t ht;obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp ht;exact hdiv i)
  let Q₀:=Q\wheelFamilyRim C
  let H₀:V→U→Prop:=fun v t=>H v t∧¬wheelFamilySpokes C v t
  have hbudget:L+c*a*Fintype.card V≤ρ₀*Fintype.card V:=by
    have hs:=mul_le_mul_of_nonneg_right haC hnR.le
    have ht:=mul_le_mul_of_nonneg_right hρ₀' hnR.le
    nlinarith only [hs,ht,hLρ,hL]
  have hdegC (t:V):((wheelFamilyRim C).degree t:ℝ)≤c*a*Fintype.card V:=by
    have hh:=hdeg t;try simp only [Finset.card_univ] at hh
    have hs:12≤c:=by dsimp [c];linarith only [show (0:ℝ)≤m from Nat.cast_nonneg m]
    exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs ha.le) hnR.le)
  have hrowC (t:V):((Finset.univ.filter (wheelFamilySpokes C t)).card:ℝ)≤c*a*Fintype.card V:=by
    have hh:=hCr t;try simp only [Finset.card_univ] at hh
    have hs:6≤c:=by dsimp [c];linarith only [show (0:ℝ)≤m from Nat.cast_nonneg m]
    exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs ha.le) hnR.le)
  have hcolC (t:U):((Finset.univ.filter (fun v=>wheelFamilySpokes C v t)).card:ℝ)≤c*a*Fintype.card V:=by
    have hh:=hCc t;try simp only [Finset.card_univ] at hh
    have hs:3*(m+1:ℝ)≤c:=by dsimp [c];linarith
    have ht:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs ha.le) hnR.le
    push_cast at hh
    nlinarith only [hh,ht]
  have hQ₀ (t:V):((changed ((rawWheelGraph P σ).neighborFinset t) (Q₀.neighborFinset t)).card:ℝ)≤ρ₀*Fintype.card V:=by
    have hh:=(Nat.cast_le (α:=ℝ)).mpr (changed_card_triangle ((rawWheelGraph P σ).neighborFinset t) (Q.neighborFinset t) (Q₀.neighborFinset t)) 
    rw [Nat.cast_add,wheel_family_rim_deletion_change] at hh
    exact hh.trans ((add_le_add (hQR t) (hdegC t)).trans hbudget)
  have hH₀r (t:V):((changed (Finset.univ.filter (rawWheelSpokes π d σ j t)) (Finset.univ.filter (H₀ t))).card:ℝ)≤ρ₀*Fintype.card V:=by
    have hh:=(Nat.cast_le (α:=ℝ)).mpr (changed_card_triangle (Finset.univ.filter (rawWheelSpokes π d σ j t)) (Finset.univ.filter (H t)) (Finset.univ.filter (H₀ t))) 
    rw [Nat.cast_add,wheel_family_spoke_row_deletion_change] at hh
    exact hh.trans ((add_le_add (hHr t) (hrowC t)).trans hbudget)
  have hH₀c (t:U):((changed (Finset.univ.filter (fun v=>rawWheelSpokes π d σ j v t)) (Finset.univ.filter (fun v=>H₀ v t))).card:ℝ)≤ρ₀*Fintype.card V:=by
    have hh:=(Nat.cast_le (α:=ℝ)).mpr (changed_card_triangle (Finset.univ.filter (fun v=>rawWheelSpokes π d σ j v t)) (Finset.univ.filter (fun v=>H v t)) (Finset.univ.filter (fun v=>H₀ v t))) 
    rw [Nat.cast_add,wheel_family_spoke_column_deletion_change] at hh
    exact hh.trans ((add_le_add (hHc t) (hcolC t)).trans hbudget)
  have hLbig:L≤ρ₀*Fintype.card V:=
    (le_add_of_nonneg_right (show 0≤c*a*Fintype.card V by positivity)).trans hbudget
  have hxX (i:Fin nr):x i∉X:=by simp only [X,Finset.mem_sdiff,Finset.mem_univ,true_and,not_not];exact hxI i
  have huB (i:Fin nh):u i∉B:=by simp only [B,Finset.mem_sdiff,Finset.mem_univ,true_and,not_not];exact huJ i
  obtain ⟨Mh,hMh,hunion,hMhdeg,Cr,hCr',hcross,hunique,hdegR,hrowR,hcolR,hcrossM⟩:=hσ.2 Q₀ H₀ (ρ₀*Fintype.card V)
    (sdiff_le.trans hQP) (by positivity) le_rfl (fun t=>(hFL t).trans hLbig)
    (fun t=>by convert hQ₀ t using 1 <;> congr!)
    (fun t=>by convert hH₀r t using 1 <;> congr!)
    (fun t=>by convert hH₀c t using 1 <;> congr!)
    X (by simpa only [Finset.card_univ,γ] using hXloss) nh u hu (hnh.trans hLbig) huB
    (fun i=>by convert hgeo.2.2 (u i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) using 1 <;> congr!)
    (fun i=>by convert hbalance'.2 (u i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) using 1 <;> congr!)
    nr x hnr hx hxX
    (fun i=>by convert hgeo.1 (x i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) using 1 <;> congr!)
    (fun i t h=>hFx i t h.1)
    (fun i=>by convert hbalance'.1 (x i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) using 1 <;> congr!)
    (fun i=>hgeo.2.1 (x i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))
  obtain ⟨M,hM,_,hMrim,hMrow,hMcol,hMdeg,hMrowdeg,hMcoldeg,horigin⟩:=ordinary_hub_row_union_packing_with_origins
    Mh u (fun i=>Finset.univ.filter (fun v=>H₀ v (u i)))
    (by convert hunion using 1 <;> congr!) (fun i=>by congr!) hMh
    (fun v=>by convert hMhdeg v using 1 <;> congr!) X B huB Cr x hxX hCr' hcross
  clear hσ joint pp pd hp' hd' hpre hdeep
  have hsupport₀:=ordinary_hub_row_union_support (by omega) Mh u hu
    (fun i=>Finset.univ.filter (fun v=>H₀ v (u i))) X B
    (fun i=>by convert hgeo.2.2 (u i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) using 1 <;> congr!)
    (by convert hunion using 1 <;> congr!) Cr x hCr' (fun i W hW=>(hunique i W hW i).mpr rfl)
    (fun i=>hgeo.2.1 (x i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)) M horigin
  have hsupport:∀ W∈M,
      (∃ i,ordinaryWheelHub W=u i ∧ ∀ v∈(ordinaryWheelRim W).support,v∉I) ∨
      (∃ i,x i∈(ordinaryWheelRim W).support ∧ ordinaryWheelHub W∉J ∧
        ∀ v∈(ordinaryWheelRim W).support,v=x i∨v∉I):=by
    intro W hW
    rcases hsupport₀ W hW with ⟨i,hi,hv⟩|⟨i,hroot,hB',hv⟩
    · exact Or.inl ⟨i,hi,fun v hh=>(Finset.mem_sdiff.mp (hv v hh)).2⟩
    · refine Or.inr ⟨i,hroot,(Finset.mem_sdiff.mp hB').2,?_⟩
      intro v hh
      exact (hv v hh).imp_right (fun h=>(Finset.mem_sdiff.mp h).2)
  have hME:=ordinary_deep_packing_avoids_inner M I J u x Q H (by
    intro W hW
    rcases hsupport W hW with hh|⟨i,_,hi,hv⟩
    · exact Or.inl hh
    · exact Or.inr ⟨i,hi,hv⟩)
  have hMrim':∀ i v,(ordinaryWheelRimGraph M).Adj (x i) v↔(Q\wheelFamilyRim C).Adj (x i) v:=by
    intro i v;convert hMrim i v using 1 <;> congr!
  obtain ⟨P',hP',_,hPinner,_,_,hPr,hProw,hPcol⟩:=prescribed_deep_packing_union C hC _ e hinner M hM hME x u hMrim' hMrow hMcol
  refine ⟨C,hC,hinner,?_,?_,?_,M,hM,?_,?_,?_,?_,?_,?_,hsupport,P',hP',hPinner,hPr,hProw,hPcol⟩
  · simpa only [Finset.card_univ] using hdeg
  · simpa only [Finset.card_univ] using hCr
  · simpa only [Finset.card_univ,Nat.cast_add,Nat.cast_one] using hCc
  · intro i t;convert hMrim i t using 1 <;> congr!
  · intro i t;exact hMrow i t
  · intro i t;exact hMcol i t
  · intro t ht;convert hMdeg t (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,ht⟩) using 1 <;> congr!
  · intro t ht;convert hMrowdeg t (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,ht⟩) using 1 <;> congr!
  · intro t ht;convert hMcoldeg t (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,ht⟩) using 1 <;> congr!

end Oberwolfach
