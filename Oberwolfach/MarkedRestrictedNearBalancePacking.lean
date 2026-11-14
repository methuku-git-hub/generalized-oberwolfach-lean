module

public import Oberwolfach.MarkedNearBalancePacking
public import Oberwolfach.OccurrenceRestrictionCuts
public import Oberwolfach.MarkedCanonicalPathCountRestriction

@[expose] public section

/-! Approximate packing in the actual host left after a reservation.
The permitted reservation loss is fixed before the desired packing
remainder. Reserved edges are not counted as uncovered edges. The original
weights and spoke profiles are restricted without being recomputed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_restricted_near_balance_packing (α p₀ : ℝ)
    (hα : 0<α) (hαmax : α≤1) (hp₀ : 0<p₀) (hp₀max : p₀≤1/2) :
    ∃ c₀ : ℕ,∀ k : ℕ,c₀≤k+2 → ∀ β L bminus bplus ω h δ : ℝ,
    0<β → 1≤L → 0<bminus → 0<bplus → 0<ω → 0<h → 0<δ → δ<1/4 →
    ∃ ε η₀ δ₀ σ : ℝ,0<ε ∧ 0<η₀ ∧ 0<δ₀ ∧ 0<σ ∧
    ∀ γ : ℝ,0<γ → ∃ ηbal : ℝ,0<ηbal ∧ ∀ b : ℕ,∃ n₀ : ℕ,
    ∀ η : ℝ,0≤η → η≤ηbal →
    ∀ (V E K U : Type)
      [Fintype V] [Fintype E] [Fintype K] [Fintype U] [DecidableEq V] [DecidableEq U],
    ∀ (tail head : E → V) (ktail khead : K → V) (π : Equiv.Perm V),
    Function.Injective (markedPhysicalEdge tail head ktail khead π) →
    ∀ (p D : ℝ),p₀≤p → p≤1/2 → n₀≤Fintype.card V →
    (Fintype.card V:ℝ)/2≤D → D≤2*Fintype.card V →
    (∀ x,|occurrenceDegree tail x-p*D|≤ε*Fintype.card V) →
    (∀ x,|occurrenceDegree head x-p*D|≤ε*Fintype.card V) →
    (∀ x,|occurrenceDegree ktail x-p*D/(k+1:ℝ)|≤ε*Fintype.card V) →
    (∀ x,|occurrenceDegree khead x-p*D/(k+1:ℝ)|≤ε*Fintype.card V) →
    (∀ x y,x≠y → 4*α*p^2*Fintype.card V≤
      ((Finset.univ.filter (fun z => (∃ e,tail e=x ∧ head e=z) ∧ (∃ e,tail e=z ∧ head e=y))).card:ℝ)) →
    (∀ S T : Finset V,(1-2*min (α/16) (p/128))*Fintype.card V<(S.card:ℝ)+T.card →
      4*(α*p/16)*Fintype.card V*min (S.card:ℝ) T.card≤
      ((Finset.univ.filter (fun e => tail e∈S ∧ head e∈T)).card:ℝ)) →
    ∀ H₀ Hₖ : V → U → Prop,
    (∀ v u,¬(H₀ v u ∧ Hₖ v u)) →
    (∀ C' : MarkedCycleTuple tail head ktail khead (k+1) π b,
      4*β*Fintype.card V≤(Fintype.card {u // MarkedHubCompatible H₀ Hₖ C'.val u}:ℝ)) →
    ω*Fintype.card V≤Fintype.card U → Fintype.card U≤Fintype.card V →
    ∀ (ps qs : Bool → U → ℝ) (δsp Dexc : ℝ),
    (∀ j,SparseIntersectionData (if j then Hₖ else H₀) (ps j) (qs j) L δsp Dexc) →
    δsp+Dexc/(Fintype.card V:ℝ)+1/(Fintype.card U:ℝ)≤δ₀ →
    ∀ i : Bool → Fin (k+2),(∀ j,markedPositionType (i j)=j) →
    (∀ u u' : U,u≠u' → 4*β*(Fintype.card V:ℝ)^(k+2)≤
      (Fintype.card (CommonMarkedCycle tail head ktail khead (k+1) π b H₀ Hₖ u u'):ℝ)) →
    (∀ j,∀ Q : BipartiteFourCycle (if j then Hₖ else H₀),
      4*β*(Fintype.card V:ℝ)^(k+1)≤
      (Fintype.card (CanonicalCommonMarkedPath tail head ktail khead (k+1) π b H₀ Hₖ (i j)
        Q.val.1.1 Q.val.1.2 Q.val.2.1 Q.val.2.2):ℝ)) →
    ∀ ψ : MarkedWheel tail head ktail khead (k+1) π b H₀ Hₖ → ℝ,
    (∀ e,|markedWheelRimLoad ψ e-1|≤η₀) →
    (∀ j v u,|markedSpokeResidual ψ j v u|≤η₀) →
    (∀ W,bminus/(Fintype.card V:ℝ)^(k+1)≤ψ W ∧ ψ W≤bplus/(Fintype.card V:ℝ)^(k+1)) →
    BipartiteLargeCut (occurrenceMultiplicity tail head) δ (2*h) →
    BipartiteLargeCut (occurrenceMultiplicity ktail khead) δ (2*h) →
    BipartiteLargeCut (relationMultiplicity H₀) δ (2*h) →
    BipartiteLargeCut (relationMultiplicity Hₖ) δ (2*h) →
    ∀ (PE:E→Prop) (PK:K→Prop) (H₀' Hₖ':V→U→Prop),
    (∀ v u,H₀' v u→H₀ v u) → (∀ v u,Hₖ' v u→Hₖ v u) →
    (∀ v,(∑ e,if ¬PE e∧tail e=v then (1:ℝ) else 0)≤σ*Fintype.card V ∧
      (∑ e,if ¬PE e∧head e=v then (1:ℝ) else 0)≤σ*Fintype.card V ∧
      (∑ e,if ¬PK e∧ktail e=v then (1:ℝ) else 0)≤σ*Fintype.card V ∧
      (∑ e,if ¬PK e∧khead e=v then (1:ℝ) else 0)≤σ*Fintype.card V ∧
      (∑ u,if H₀ v u∧¬H₀' v u then (1:ℝ) else 0)≤σ*Fintype.card V ∧
      (∑ u,if Hₖ v u∧¬Hₖ' v u then (1:ℝ) else 0)≤σ*Fintype.card V) →
    (∀ u,(∑ v,if H₀ v u∧¬H₀' v u then (1:ℝ) else 0)≤σ*Fintype.card V ∧
      (∑ v,if Hₖ v u∧¬Hₖ' v u then (1:ℝ) else 0)≤σ*Fintype.card V) →
    let t':=fun e:{e//PE e}=>tail e.val
    let h':=fun e:{e//PE e}=>head e.val
    let kt':=fun e:{e//PK e}=>ktail e.val
    let kh':=fun e:{e//PK e}=>khead e.val;
    (∀ v,|occurrenceDegree (Sum.elim t' kt') v-
      (∑ u,if H₀' v u then (1:ℝ) else 0)-(∑ u,if Hₖ' v u then (1:ℝ) else 0)|≤η*Fintype.card V) →
    (∀ v,|occurrenceDegree (Sum.elim h' kh') v-
      (∑ u,if H₀' v u then (1:ℝ) else 0)-(∑ u,if Hₖ' v u then (1:ℝ) else 0)|≤η*Fintype.card V) →
    (∀ v,|occurrenceDegree kh' v-(∑ u,if Hₖ' v u then (1:ℝ) else 0)|≤η*Fintype.card V) →
    (∀ u,|(∑ v,if H₀' v u then (1:ℝ) else 0)-(k+1:ℝ)*(∑ v,if Hₖ' v u then (1:ℝ) else 0)|≤η*Fintype.card V) →
    ∃ M : Finset (MarkedWheel t' h' kt' kh' (k+1) π b H₀' Hₖ'),
      (∀ W∈M,∀ Z∈M,W≠Z → Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z)) ∧
      (∀ x : V⊕U,((markedIncidentEdges t' h' kt' kh' π H₀' Hₖ' false x \
        M.biUnion markedActiveResources).card : ℝ)≤γ*Fintype.card V) ∧
      (∀ x : V⊕U,((markedPhysicalIncidentEdges t' h' kt' kh' π H₀' Hₖ' x \
        M.biUnion markedWheelPhysicalResources).card : ℝ)≤γ*Fintype.card V) := by
  obtain ⟨c₀,hc₀⟩:=marked_near_balance_wheel_packing α p₀ hα hαmax hp₀ hp₀max
  refine ⟨max c₀ 4,?_⟩
  intro k hk β L bminus bplus ω h δ hβ hL hbm hbp hω hh hδ hδsmall
  have hkm:3≤k+1:=by omega
  let c:ℝ:=(k:ℝ)+2
  have hc:0<c:=by dsimp only [c];positivity
  obtain ⟨ε,η₀,δ₀,hε,hη,hδ₀,hpacking⟩:=hc₀ k ((le_max_left _ _).trans hk)
    β L bminus bplus ω h δ hβ hL hbm hbp hω hh hδ hδsmall
  let σ:=min (ε/2) (min (α*p₀^2/4) (min (α*p₀/32)
    (min (β/(8*c)) (min (η₀/(32*c^4*bplus))
      (min (δ₀*ω/(12*(L^2+ω))) (min (h/2) (h*ω/2)))))))
  have hσ:0<σ:=by dsimp only [σ];positivity
  have hsε:σ≤ε/2:=by dsimp only [σ];exact min_le_left _ _
  have hs2:σ≤α*p₀^2/4:=by dsimp only [σ];exact (min_le_right _ _).trans (min_le_left _ _)
  have hsCut:σ≤α*p₀/32:=by dsimp only [σ];exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsCount:σ≤β/(8*c):=by dsimp only [σ];exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsLoad:σ≤η₀/(32*c^4*bplus):=by dsimp only [σ];exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hsData:σ≤δ₀*ω/(12*(L^2+ω)):=by dsimp only [σ];exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hsH:σ≤min (h/2) (h*ω/2):=by dsimp only [σ];exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  refine ⟨ε/2,η₀/2,δ₀/2,σ,by positivity,by positivity,by positivity,hσ,?_⟩
  intro γ hγ
  obtain ⟨ηbal,hηbal,hpack⟩:=hpacking γ hγ
  refine ⟨ηbal,hηbal,?_⟩
  intro b
  obtain ⟨N,hN⟩:=hpack b
  refine ⟨max 1 N,?_⟩
  intro η hηsmall hηbalSmall V E K U _ _ _ _ _ _ tail head ktail khead π hphys p D hp hpmax hn hDlo hDhi
    hdo hdi hdko hdki htwo hcut H₀ Hₖ hdisj hhub hωn huV ps qs δsp Dexc hdata hsmall i hipos
    hcommon hpaths ψ hRerr hSerr hψ hcut0 hcutK hcutH0 hcutHK PE PK H₀' Hₖ' hH0 hHK hV hU
    t' h' kt' kh' hbp0 hbm0 hbk hbw
  let n:ℝ:=Fintype.card V
  have hnpos:0<Fintype.card V:=by omega
  have hnreal:0<n:=by change 0<(Fintype.card V:ℝ);exact_mod_cast hnpos
  have hu:0<Fintype.card U:=by
    have ht:0<(Fintype.card U:ℝ):=(mul_pos hω hnreal).trans_le hωn
    exact_mod_cast ht
  have hωmax:ω≤1:=by
    have huR:(Fintype.card U:ℝ)≤n:=by
      change (Fintype.card U:ℝ)≤(Fintype.card V:ℝ)
      exact_mod_cast huV
    change ω*n≤_ at hωn
    nlinarith
  let d:=σ*n
  have hd:0≤d:=by dsimp only [d];positivity
  obtain ⟨hinj,hkinj⟩:=markedPhysicalEdge_endpoint_injections tail head ktail khead π hphys
  have hEout (v:V):(∑ e,if ¬PE e∧tail e=v then (1:ℝ) else 0)≤d:=(hV v).1
  have hEin (v:V):(∑ e,if ¬PE e∧head e=v then (1:ℝ) else 0)≤d:=(hV v).2.1
  have hKout (v:V):(∑ e,if ¬PK e∧ktail e=v then (1:ℝ) else 0)≤d:=(hV v).2.2.1
  have hKin (v:V):(∑ e,if ¬PK e∧khead e=v then (1:ℝ) else 0)≤d:=(hV v).2.2.2.1
  have hH0row (v:V):(∑ u,if H₀ v u∧¬H₀' v u then (1:ℝ) else 0)≤d:=(hV v).2.2.2.2.1
  have hHKrow (v:V):(∑ u,if Hₖ v u∧¬Hₖ' v u then (1:ℝ) else 0)≤d:=(hV v).2.2.2.2.2
  have hH0col (u:U):(∑ v,if H₀ v u∧¬H₀' v u then (1:ℝ) else 0)≤d:=(hU u).1
  have hHKcol (u:U):(∑ v,if Hₖ v u∧¬Hₖ' v u then (1:ℝ) else 0)≤d:=(hU u).2
  have hdε : d≤(ε/2)*n := mul_le_mul_of_nonneg_right hsε hnreal.le
  have hdegree {A : Type} [Fintype A] (f : A → V) (keep : A → Prop) (μ : ℝ)
      (hbase : ∀ x,|occurrenceDegree f x-μ|≤(ε/2)*n)
      (hdel : ∀ x,(∑ a,if ¬keep a ∧ f a=x then (1:ℝ) else 0)≤d) :
      ∀ x,|occurrenceDegree (fun a : {a // keep a}=>f a.val) x-μ|≤ε*n := by
    intro x
    have hh := occurrenceDegree_restriction_target f keep x μ ((ε/2)*n) d (hbase x) (by convert hdel x using 1 <;> congr!)
    linarith only [hh,hdε]
  have hd0 := hdegree tail PE (p*D) hdo (by convert hEout using 1 <;> congr!)
  have hdi0 := hdegree head PE (p*D) hdi (by convert hEin using 1 <;> congr!)
  have hdk0 := hdegree ktail PK (p*D/(k+1:ℝ)) hdko (by convert hKout using 1 <;> congr!)
  have hdki0 := hdegree khead PK (p*D/(k+1:ℝ)) hdki (by convert hKin using 1 <;> congr!)
  have hp2 : p₀^2≤p^2 := pow_le_pow_left₀ hp₀.le hp 2
  have htwoCost : 2*d≤α*p^2*n := by
    have h1 := mul_le_mul_of_nonneg_right hs2 hnreal.le
    have h2 := mul_le_mul_of_nonneg_left hp2 (mul_nonneg hα.le hnreal.le)
    dsimp only [d]
    nlinarith only [h1,h2,mul_nonneg hσ.le hnreal.le]
  have htwo' (x y : V) (hxy : x≠y) : 2*α*p^2*n≤
      ((Finset.univ.filter (fun z=>(∃ e : {e // PE e},tail e.val=x ∧ head e.val=z) ∧
        (∃ e : {e // PE e},tail e.val=z ∧ head e.val=y))).card:ℝ) := by
    have hbase := htwo x y hxy
    have hloss := represented_two_step_deletion tail head PE x y d (by convert hEout x using 1 <;> congr!) (by convert hEin y using 1 <;> congr!)
    have hh := (abs_le.mp hloss).1
    change 4*α*p^2*n≤_ at hbase
    nlinarith only [hh,hbase,htwoCost,mul_nonneg hα.le (mul_nonneg (sq_nonneg p) hnreal.le)]
  have hcutCost : d≤(α*p/16)*n := by
    have h1 := mul_le_mul_of_nonneg_right hsCut hnreal.le
    have h2 := mul_le_mul_of_nonneg_left hp (mul_nonneg hα.le hnreal.le)
    dsimp only [d]
    nlinarith only [h1,h2,mul_nonneg hσ.le hnreal.le]
  have hcut' (S T : Finset V)
      (hST : (1-2*min (α/16) (p/128))*n<(S.card:ℝ)+T.card) :
      2*(α*p/16)*n*min (S.card:ℝ) T.card≤
        ((Finset.univ.filter (fun e : {e // PE e}=>tail e.val∈S ∧ head e.val∈T)).card:ℝ) := by
    have hbase := hcut S T hST
    have hloss:=occurrence_cut_restriction_loss hnpos tail head hinj PE d hd
      (by convert hEout using 1 <;> congr!) (by convert hEin using 1 <;> congr!) S T
    have hs : 0≤min (S.card:ℝ) T.card := by positivity
    have hh := mul_le_mul_of_nonneg_right hcutCost hs
    change 4*(α*p/16)*n*min (S.card:ℝ) T.card≤_ at hbase
    have hi : 2*(α*p/16)*n*min (S.card:ℝ) T.card≤
        ((Finset.univ.filter (fun e : E=>tail e∈S ∧ head e∈T)).card:ℝ)-d*min (S.card:ℝ) T.card := by
      have ht:0≤(α*p/16)*n*min (S.card:ℝ) T.card:=by
        have hp':0≤p:=hp₀.le.trans hp
        positivity
      nlinarith only [hbase,hh,ht]
    convert (hi.trans (by convert hloss using 1 <;> congr!)) using 1 <;> congr!
  have hcountCost : 4*c*d≤β*n := by
    have hs := (le_div_iff₀ (by positivity : 0<8*c)).mp hsCount
    have hh := mul_le_mul_of_nonneg_right hs hnreal.le
    have hnon : 0≤c*d := mul_nonneg hc.le hd
    dsimp only [d] at hnon ⊢
    nlinarith only [hh,hnon]
  have hcEq : ((k+1:ℕ):ℝ)+1=c := by dsimp only [c];push_cast;ring
  have hhub' := marked_hub_count_restriction PE PK hH0 hHK (2*β) d
    (by rw [hcEq];nlinarith only [hcountCost,mul_nonneg hc.le hd]) (by convert hH0row using 1 <;> congr!) (by convert hHKrow using 1 <;> congr!) (by intro C;convert hhub C using 1 <;> ring)
  have hcommon' (u u' : U) (hne : u≠u') : 2*β*n^(k+2)≤
      (Fintype.card (CommonMarkedCycle (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
        (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) (k+1) π b H₀' Hₖ' u u'):ℝ) := by
    have hh := marked_common_cycle_count_restriction (by omega : 1≤k+1) PE PK (2*β) d
      (by rw [hcEq];nlinarith only [hcountCost,mul_nonneg hc.le hd]) (by convert hEout using 1 <;> congr!) (by convert hKout using 1 <;> congr!) (by convert hH0col using 1 <;> congr!) (by convert hHKcol using 1 <;> congr!) u u' (by convert hcommon u u' hne using 1 <;> ring)
    convert hh using 1 <;> congr!
  have htyped (j : Bool) (v : V) (u : U) :
      (if j then Hₖ' else H₀') v u → (if j then Hₖ else H₀) v u := by
    cases j
    · exact hH0 v u
    · exact hHK v u
  have hpaths' (j : Bool) (Q : BipartiteFourCycle (if j then Hₖ' else H₀')) :
      2*β*n^(k+1)≤
      (Fintype.card (CanonicalCommonMarkedPath (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
        (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) (k+1) π b H₀' Hₖ' (i j)
        Q.val.1.1 Q.val.1.2 Q.val.2.1 Q.val.2.2):ℝ) := by
    let Qp : BipartiteFourCycle (if j then Hₖ else H₀) :=
      ⟨Q.val,Q.property.1,Q.property.2.1,htyped j _ _ Q.property.2.2.1,
        htyped j _ _ Q.property.2.2.2.1,htyped j _ _ Q.property.2.2.2.2.1,
        htyped j _ _ Q.property.2.2.2.2.2⟩
    have hh := marked_canonical_path_count_restriction (by omega : 1≤k+1) PE PK (2*β) d
      (by rw [hcEq];nlinarith only [hcountCost,mul_nonneg hβ.le hnreal.le]) (by convert hEout using 1 <;> congr!) (by convert hEin using 1 <;> congr!) (by convert hKout using 1 <;> congr!) (by convert hKin using 1 <;> congr!) (by convert hH0col using 1 <;> congr!) (by convert hHKcol using 1 <;> congr!)
      (i j) Q.val.1.1 Q.val.1.2 Q.val.2.1 Q.val.2.2 (by convert hpaths j Qp using 1 <;> ring)
    convert hh using 1 <;> congr!
  let ρ := 6*(L^2+ω)*σ/ω
  have hρ : 0≤ρ := by dsimp only [ρ];positivity
  have hρid : ρ*ω=6*(L^2+ω)*σ := by dsimp only [ρ];field_simp
  have hρsmall : ρ≤δ₀/2 := by
    have hs := (le_div_iff₀ (by positivity : 0<12*(L^2+ω))).mp hsData
    change 6*(L^2+ω)*σ/ω≤δ₀/2
    apply (div_le_iff₀ hω).mpr
    nlinarith only [hs]
  have hcolScale : 3*d≤ρ*n := by
    have hr : 6*σ≤ρ := by
      apply (le_div_iff₀ hω).mpr
      nlinarith only [mul_nonneg (sq_nonneg L) hσ.le]
    have hh := mul_le_mul_of_nonneg_right hr hnreal.le
    dsimp only [d]
    nlinarith only [hh,mul_nonneg hσ.le hnreal.le]
  have hrowScale : 2*L^2*d≤ρ*Fintype.card U := by
    have hh := mul_le_mul_of_nonneg_left hωn hρ
    have he := congrArg (fun z : ℝ=>z*n) hρid
    have h1 : 0≤L^2*σ*n := by positivity
    have h2 : 0≤ω*σ*n := by positivity
    dsimp only [d]
    nlinarith only [hh,he,h1,h2]
  have hdata' (j : Bool) : SparseIntersectionData (if j then Hₖ' else H₀')
      (ps j) (qs j) L (δsp+ρ) Dexc := by
    apply (hdata j).deletion (if j then Hₖ' else H₀') (htyped j) d ρ hd hρ
    · intro v
      cases j
      · simpa only [Bool.false_eq_true,ite_false,bipAdj] using hH0row v
      · simpa only [ite_true,bipAdj] using hHKrow v
    · intro u
      cases j
      · simpa only [Bool.false_eq_true,ite_false,bipAdj] using hH0col u
      · simpa only [ite_true,bipAdj] using hHKcol u
    · exact hcolScale
    · exact hrowScale
  have hsmall' : (δsp+ρ)+Dexc/n+1/(Fintype.card U:ℝ)≤δ₀ := by
    change δsp+Dexc/n+1/(Fintype.card U:ℝ)≤δ₀/2 at hsmall
    linarith only [hsmall,hρsmall]
  have haggOut (x : V) :
      (∑ e,if ¬Sum.elim PE PK e ∧ Sum.elim tail ktail e=x then (1:ℝ) else 0)≤2*d := by
    simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]
    have he : (∑ e,if ¬PE e ∧ tail e=x then (1:ℝ) else 0)≤d := by convert hEout x using 1 <;> congr!
    have hk : (∑ e,if ¬PK e ∧ ktail e=x then (1:ℝ) else 0)≤d := by convert hKout x using 1 <;> congr!
    exact add_le_add he hk |>.trans (by ring_nf;exact le_rfl)
  have haggIn (x : V) :
      (∑ e,if ¬Sum.elim PE PK e ∧ Sum.elim head khead e=x then (1:ℝ) else 0)≤2*d := by
    simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]
    have he : (∑ e,if ¬PE e ∧ head e=x then (1:ℝ) else 0)≤d := by convert hEin x using 1 <;> congr!
    have hk : (∑ e,if ¬PK e ∧ khead e=x then (1:ℝ) else 0)≤d := by convert hKin x using 1 <;> congr!
    exact add_le_add he hk |>.trans (by ring_nf;exact le_rfl)
  have haggRow (x : V) :
      (∑ u,bipAdj (fun x u=>(H₀ x u ∨ Hₖ x u) ∧ ¬(H₀' x u ∨ Hₖ' x u)) x u)≤2*d := by
    convert deleted_spoke_union_row_sum_le H₀ Hₖ H₀' Hₖ' x d (by convert hH0row x using 1 <;> congr!) (by convert hHKrow x using 1 <;> congr!) using 1 <;> simp only [bipAdj] <;> congr!
  have haggCol (u : U) :
      (∑ x,bipAdj (fun x u=>(H₀ x u ∨ Hₖ x u) ∧ ¬(H₀' x u ∨ Hₖ' x u)) x u)≤2*d := by
    convert deleted_spoke_union_col_sum_le H₀ Hₖ H₀' Hₖ' u d (by convert hH0col u using 1 <;> congr!) (by convert hHKcol u using 1 <;> congr!) using 1 <;> simp only [bipAdj] <;> congr!
  let ψ' := fun W=>ψ (markedWheelToLarger PE PK hH0 hHK W)
  obtain ⟨hψ',hR',hS'⟩ := marked_approximate_weights_restriction hkm hphys hnpos huV PE PK hH0 hHK hdisj
    ψ bminus bplus (η₀/2) (2*d) hbm.le hbp.le (by positivity) (by positivity) hψ hRerr hSerr
    haggOut haggIn haggRow haggCol
  have hloadCost : 8*((k+1:ℝ)+1)^4*bplus*(2*d)/n≤η₀/2 := by
    have hs := (le_div_iff₀ (by positivity : 0<32*c^4*bplus)).mp hsLoad
    have he : 8*((k+1:ℝ)+1)^4*bplus*(2*d)/n=16*c^4*bplus*σ := by
      dsimp only [c,d]
      field_simp
      ring
    rw [he]
    nlinarith only [hs]
  have hR'' (e : {e // PE e}⊕{e // PK e}) : |markedWheelRimLoad ψ' e-1|≤η₀ := by
    have hh := hR' e
    simp only [Nat.cast_add,Nat.cast_one] at hh
    linarith only [hh,hloadCost]
  have hS'' (j : Bool) (v : V) (u : U) : |markedSpokeResidual ψ' j v u|≤η₀ := by
    have hh := hS' j v u
    simp only [Nat.cast_add,Nat.cast_one] at hh
    linarith only [hh,hloadCost]
  have hphys' := markedRestrictedPhysical_injective PE PK hphys
  have hdisj' (v : V) (u : U) : ¬(H₀' v u ∧ Hₖ' v u) :=
    fun h=>hdisj v u ⟨hH0 v u h.1,hHK v u h.2⟩
  have hsH1:σ≤h:=le_trans (hsH.trans (min_le_left _ _)) (by linarith)
  have hsHω:σ/ω≤h:=by
    apply (div_le_iff₀ hω).mpr
    have ht:=hsH.trans (min_le_right _ _)
    nlinarith only [ht,mul_nonneg hh.le hω.le]
  have hcut0':BipartiteLargeCut (occurrenceMultiplicity t' h') δ h:=by
    have ht:=occurrence_bipartiteLargeCut_restriction hnpos tail head hinj PE δ (2*h) σ hσ.le
      (by convert hEout using 1 <;> congr!) (by convert hEin using 1 <;> congr!) hcut0
    apply bipartiteLargeCut_coefficient_mono _ δ (2*h-σ) h (by linarith)
    convert ht using 1 <;> congr!
  have hcutK':BipartiteLargeCut (occurrenceMultiplicity kt' kh') δ h:=by
    have ht:=occurrence_bipartiteLargeCut_restriction hnpos ktail khead hkinj PK δ (2*h) σ hσ.le
      (by convert hKout using 1 <;> congr!) (by convert hKin using 1 <;> congr!) hcutK
    apply bipartiteLargeCut_coefficient_mono _ δ (2*h-σ) h (by linarith)
    convert ht using 1 <;> congr!
  have hrowScale':d≤(σ/ω)*Fintype.card U:=by
    have ht:=mul_le_mul_of_nonneg_left hωn (by positivity:0≤σ/ω)
    dsimp only [d]
    calc
      σ*n=(σ/ω)*(ω*n):=by field_simp
      _≤_:=ht
  have hcolScale':d≤(σ/ω)*Fintype.card V:=by
    apply mul_le_mul_of_nonneg_right _ hnreal.le
    apply (le_div_iff₀ hω).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hωmax hσ.le]
  have hcutSpoke (H H':V→U→Prop) (hsub:∀ v u,H' v u→H v u)
      (hr:∀ v,(∑ u,if H v u∧¬H' v u then (1:ℝ) else 0)≤d)
      (hc:∀ u,(∑ v,if H v u∧¬H' v u then (1:ℝ) else 0)≤d)
      (hcut:BipartiteLargeCut (relationMultiplicity H) δ (2*h)):
      BipartiteLargeCut (relationMultiplicity H') δ h:=by
    have ht:=bipartiteLargeCut_subrelation V U hnpos hu H H' hsub δ (2*h) (σ/ω) (by positivity)
      (fun v=>(hr v).trans hrowScale') (fun u=>(hc u).trans hcolScale') hcut
    exact bipartiteLargeCut_coefficient_mono _ δ (2*h-σ/ω) h (by linarith) ht
  have hcutH0':=hcutSpoke H₀ H₀' hH0 hH0row hH0col hcutH0
  have hcutHK':=hcutSpoke Hₖ Hₖ' hHK hHKrow hHKcol hcutHK
  have hresult:=hN η hηsmall hηbalSmall V {e//PE e} {e//PK e} U
    t' h' kt' kh' π hphys' p D hp hpmax ((le_max_right _ _).trans hn) hDlo hDhi
    hd0 hdi0 hdk0 hdki0 (by convert htwo' using 1 <;> congr!) (by convert hcut' using 1 <;> congr!)
    H₀' Hₖ' hdisj' (by convert hhub' using 1 <;> congr!) hωn huV ps qs (δsp+ρ) Dexc hdata' hsmall' i hipos
    (by convert hcommon' using 1 <;> congr!) (by convert hpaths' using 1 <;> congr!)
    ψ' hR'' hS'' hψ'
    (occurrenceMultiplicity t' h') (occurrenceMultiplicity kt' kh') (relationMultiplicity H₀') (relationMultiplicity Hₖ')
    (fun _ _=>le_rfl) (fun _ _=>le_rfl) (fun _ _=>le_rfl) (fun _ _=>le_rfl)
    hbp0 hbm0 hbk hbw hcut0' hcutK' hcutH0' hcutHK'
  convert hresult using 1 <;> congr!
end Oberwolfach
