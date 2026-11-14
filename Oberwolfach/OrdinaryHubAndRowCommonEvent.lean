module

public import Oberwolfach.OrdinaryHubCoverCommonEvent
public import Oberwolfach.OrdinaryRowCoverEventAfterHubs

@[expose] public section

/-! A single original-law event constructs both the hub wheels and the
subsequent longer-cycle row covers. The hub packing is constructed inside
this theorem; it is not an input. Fixed counting domains precede sampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 6500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_hub_and_row_common_event (m:ℕ) (hm:3≤m) (α p ω:ℝ)
    (hα:0<α) (hp:0<p) (hp1:p≤1) (hω:0<ω):
    ∃ K:ℕ,0<K ∧ ∃ ε₀ ρ θ:ℝ,0<ε₀ ∧ 0<ρ ∧ 0<θ ∧
    ∀ Dmax d q₀:ℕ,∀ hd:2≤d,∃ N:ℕ,
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    ∀ (P F:SimpleGraph V) (π:Equiv.Perm V) (B:Finset U),N≤Fintype.card V →
      ω*Fintype.card V≤(B.card:ℝ) → Fintype.card U≤Fintype.card V →
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
      ∀ X:Finset V,((Finset.univ\X).card:ℝ)≤p^6*(min α 1)*Fintype.card V/8 →
      ∀ (nh:ℕ) (u:Fin nh→U),Function.Injective u → (2*nh:ℝ)≤L →
        (∀ i,u i∉B) → (∀ i,Finset.univ.filter (fun v=>H v (u i))⊆X) →
        (∀ i,(m+1)∣(Finset.univ.filter (fun v=>H v (u i))).card) →
      ∀ (nr:ℕ) (x:Fin nr→V),(nr:ℝ)≤θ*Fintype.card V → Function.Injective x → (∀ i,x i∉X) →
        (∀ i,Q.neighborFinset (x i)⊆X) → (∀ i a,Q.Adj (x i) a→¬F.Adj (x i) a) →
        (∀ i,Q.degree (x i)=2*(Finset.univ.filter (H (x i))).card) → (∀ i a,H (x i) a→a∈B) →
      ∃ M:Finset (OrdinaryWheel Q F H (m+1)),
        (∀ W∈M,∀ Z∈M,W≠Z→Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z)) ∧
        M.biUnion ordinaryWheelResources=(ordinaryWheelRimGraph M).edgeFinset.image Sum.inl ∪
          Finset.univ.biUnion (fun i=>(Finset.univ.filter (fun v=>H v (u i))).image (fun v=>Sum.inr (v,u i))) ∧
        (∀ v,(ordinaryWheelRimGraph M).degree v≤2*nh) ∧
        ∃ C:Fin nr→Finset (OrdinaryWheel (Q\ordinaryWheelRimGraph M) F
          (fun v a=>H v a∧¬ordinaryPackingSpokes M v a) (m+1)),
          (∀ i,OrdinaryRowCover (C i) (x i) X K) ∧
          (∀ i j,i≠j→Disjoint ((C i).biUnion ordinaryWheelResources) ((C j).biUnion ordinaryWheelResources)) ∧
          (∀ i,∀ W∈C i,∀ k,x k∈(ordinaryWheelRim W).support↔k=i) ∧
          (∀ a∈X,(ordinaryWheelRimGraph (Finset.univ.biUnion C)).degree a≤nr*(2*(K+1))) ∧
          (∀ a∈X,(Finset.univ.filter (ordinaryPackingSpokes (Finset.univ.biUnion C) a)).card≤nr*(K+1)) ∧
          (∀ a,(Finset.univ.filter (fun v=>ordinaryPackingSpokes (Finset.univ.biUnion C) v a)).card≤nr*(m+1)) ∧
          (∀ i,Disjoint ((C i).biUnion ordinaryWheelResources) (M.biUnion ordinaryWheelResources))):=by
  obtain ⟨ε₀,ρh,hε₀,hρh,hhub⟩:=ordinary_hub_cover_common_event m (by omega) α p ω hα hp hp1 hω
  obtain ⟨K,hK,θ,εr,hθ,hεr,hrow⟩:=ordinary_row_cover_event_after_hubs (m+1) (by omega) 1 α ω p le_rfl hα hω hp hp1
  let ρ:=min ρh (εr*(min 1 ω)/6)
  have hρ:0<ρ:=lt_min hρh (by positivity)
  have hρhub:ρ≤ρh:=min_le_left _ _
  have hρrow:6*ρ≤εr*min 1 ω:=by
    have hh:=min_le_right ρh (εr*(min 1 ω)/6)
    dsimp [ρ];linarith only [hh]
  refine ⟨K,hK,ε₀,ρ,θ,hε₀,hρ,hθ,?_⟩
  intro Dmax d q₀ hd
  obtain ⟨Nh,hh⟩:=hhub Dmax (Nat.cast_nonneg _) d (q₀+1) hd
  obtain ⟨Nr,hr⟩:=hrow d Dmax (q₀+1) hd
  refine ⟨max 2 (max Nh Nr),?_⟩
  intro V U Γ Color _ _ _ _ _ _ P F π B hn hB hU hP hF hclose hnoshort
    pR pH D ε hpR hpR1 hpH hpH1 hD hε hεsmall hreg hbalance q hq hQ s hs hS j hj
  have hnN:0<Fintype.card V:=by omega
  have hnR:(0:ℝ)<Fintype.card V:=Nat.cast_pos.mpr hnN
  have hUlo:ω*Fintype.card V≤(Fintype.card U:ℝ):=
    hB.trans (Nat.cast_le.mpr (Finset.card_le_univ B))
  have hProw (v:V):(1/2+α)*(Finset.univ:Finset V).card≤((Finset.univ∩P.neighborFinset v).card:ℝ):=by
    have hhalf: (1/2:ℝ)+α≤cycleThreshold (m+1)+α:=by linarith only [cycleThreshold_half_le (show 3≤m+1 by omega)]
    simpa only [Finset.card_univ,Finset.univ_inter,SimpleGraph.card_neighborFinset_eq_degree] using
      (mul_le_mul_of_nonneg_right hhalf hnR.le).trans (hP v)
  have ph:=hh V U Γ Color P (by omega) hUlo hU hP F π
    (fun v=>Nat.cast_le.mpr (hF v)) hclose hnoshort pR pH D ε hpR hpR1 hpH hpH1 hD hε hεsmall hreg hbalance q hq hQ s hs hS j hj
  have pr:=hr V U Γ Color P F π Finset.univ B (by simpa only [Finset.card_univ] using (show Nr≤Fintype.card V by omega))
    (by simp) (by simpa using (Nat.cast_le.mpr hU:(Fintype.card U:ℝ)≤Fintype.card V))
    (by simpa only [Finset.card_univ] using hB) hclose hF hProw hnoshort pR pH (hp.le.trans hpR) hpR1 hpR hpH hpH1 q hq hQ s hs hS j hj
  let μ:=FiniteLaw.pi (rawWheelLaw (fun _:Sym2 V=>pR) (fun _=>hp.le.trans hpR) (fun _=>hpR1) d hd q hq hQ s hs hS)
  have combine (E F:((e:RawWheelCoordinate V U)→RawWheelCoordinateState Γ Color e)→Prop)
      (he:1-1/(Fintype.card V:ℝ)^(q₀+1)≤μ.probability E)
      (hf:1-1/(Fintype.card V:ℝ)^(q₀+1)≤μ.probability F):
      1-1/(Fintype.card V:ℝ)^q₀≤μ.probability (fun σ=>E σ∧F σ):=by
    have hi:=finiteLaw_good_intersection μ E F (1/(Fintype.card V:ℝ)^(q₀+1)) hf
    have hb:=scaled_inverse_power_le (Fintype.card V) q₀ hnN 2 (by exact_mod_cast (show 2≤Fintype.card V by omega))
    have hb':2*(1/(Fintype.card V:ℝ)^(q₀+1))≤1/(Fintype.card V:ℝ)^q₀:=by convert hb using 1 <;> ring
    linarith only [he,hi,hb']
  have joint:=combine _ _ ph (by simpa only [Finset.card_univ] using pr)
  apply joint.trans
  apply finiteLaw_probability_mono
  intro σ hσ Q H L hQP hL hLρ hFL hQR hHr hHc X hmissing nh u hu hnh hnotB hTX hdiv nr x hnr hx hxX hroot hFx hbal hrootB
  have hLhub:L≤ρh*Fintype.card V:=hLρ.trans (mul_le_mul_of_nonneg_right hρhub hnR.le)
  have hinc (v:V):(2*(Finset.univ.filter (fun i=>H v (u i))).card:ℝ)≤ρh*Fintype.card V:=by
    have hh:(Finset.univ.filter (fun i=>H v (u i))).card≤nh:=by simpa using Finset.card_filter_le (s:=Finset.univ) (fun i=>H v (u i))
    have hh':(2*(Finset.univ.filter (fun i=>H v (u i))).card:ℝ)≤2*nh:=by exact_mod_cast Nat.mul_le_mul_left 2 hh
    exact hh'.trans (hnh.trans hLhub)
  obtain ⟨M,hM,hunion,hdeg,_⟩:=hσ.1 Q H L hQP hL hLhub hFL hQR hHr hHc nh u hu hinc hdiv
  have hMdeg (v:V):(ordinaryWheelRimGraph M).degree v≤2*nh:=
    (hdeg v).trans (Nat.mul_le_mul_left 2 (by simpa using Finset.card_filter_le (s:=Finset.univ) (fun i=>H v (u i))))
  have hLa:6*L≤εr*Fintype.card V:=by
    have hh:=mul_le_mul_of_nonneg_right hρrow hnR.le
    have hsmall:εr*(min 1 ω)*Fintype.card V≤εr*Fintype.card V:=by
      calc
        _≤εr*1*Fintype.card V:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (min_le_left _ _) hεr.le) hnR.le
        _=_:=by ring
    nlinarith only [hh,hsmall,hLρ]
  have hLb:6*L≤εr*B.card:=by
    have hh:=mul_le_mul_of_nonneg_right hρrow hnR.le
    have hsmall:εr*(min 1 ω)*Fintype.card V≤εr*B.card:=by
      calc
        _≤εr*ω*Fintype.card V:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (min_le_right _ _) hεr.le) hnR.le
        _=εr*(ω*Fintype.card V):=by ring
        _≤_:=mul_le_mul_of_nonneg_left hB hεr.le
    nlinarith only [hh,hsmall,hLρ]
  have hHrB (v:V):((changed (B∩Finset.univ.filter (rawWheelSpokes π d σ j v)) (B∩Finset.univ.filter (H v))).card:ℝ)≤L:=by
    apply le_trans _ (hHr v)
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro a ha
    simp only [changed,Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter] at ha ⊢
    tauto
  obtain ⟨C,hC⟩:=hσ.2 Q H L hL (by simpa only [Finset.card_univ] using hLa) hLb hQP
    (fun v=>by simpa only [Finset.univ_inter] using hQR v) hHrB
    (fun a _=>by simpa only [Finset.univ_inter] using hHc a)
    X (Finset.subset_univ _) (by simpa only [Finset.card_univ] using hmissing)
    nr x (by simpa only [Finset.card_univ] using hnr) hx hxX hroot hFx hbal hrootB
    nh u hu (fun i=>Finset.univ.filter (fun v=>H v (u i))) M hTX hnotB hnh hMdeg hunion
  exact ⟨M,hM,hunion,hMdeg,C,hC⟩

end Oberwolfach
