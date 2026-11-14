module

public import Oberwolfach.MarkedBalancedWheelPacking
public import Oberwolfach.MarkedDeletedIncidence
public import Oberwolfach.MarkedApproximateWeightRestriction
public import Oberwolfach.MarkedExtensionCountRestriction
public import Oberwolfach.SparseIntersectionDeletion
public import Oberwolfach.OccurrenceDegreeDeletion
public import Oberwolfach.DirectedRelationDeletion

@[expose] public section

/-! Marked packing after a small, exactly balancing deletion. All parent
profiles and weights are retained. Host and load tolerances precede the
leftover tolerance; the admissible deletion fraction precedes separation.
The existence of the balancing deletion is established separately by
sparse_typed_host_correction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_small_deletion_packing (α p₀ : ℝ)
    (hα : 0<α) (hαmax : α≤1) (hp₀ : 0<p₀) (hp₀max : p₀≤1/2) :
    ∃ c₀ : ℕ,∀ k : ℕ,c₀≤k+2 → ∀ β L bminus bplus ω : ℝ,
    0<β → 1≤L → 0<bminus → 0<bplus → 0<ω →
    ∃ ε η₀ δ₀ : ℝ,0<ε ∧ 0<η₀ ∧ 0<δ₀ ∧
    ∀ γ : ℝ,0<γ → ∃ σ : ℝ,0<σ ∧ ∀ b : ℕ,∃ n₀ : ℕ,
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
    (∀ x y,x≠y → 2*α*p^2*Fintype.card V≤
      ((Finset.univ.filter (fun z => (∃ e,tail e=x ∧ head e=z) ∧ (∃ e,tail e=z ∧ head e=y))).card:ℝ)) →
    (∀ S T : Finset V,(1-2*min (α/16) (p/128))*Fintype.card V<(S.card:ℝ)+T.card →
      2*(α*p/16)*Fintype.card V*min (S.card:ℝ) T.card≤
      ((Finset.univ.filter (fun e => tail e∈S ∧ head e∈T)).card:ℝ)) →
    ∀ H₀ Hₖ : V → U → Prop,
    (∀ v u,¬(H₀ v u ∧ Hₖ v u)) →
    (∀ C' : MarkedCycleTuple tail head ktail khead (k+1) π b,
      2*β*Fintype.card V≤(Fintype.card {u // MarkedHubCompatible H₀ Hₖ C'.val u}:ℝ)) →
    ω*Fintype.card V≤Fintype.card U → Fintype.card U≤Fintype.card V →
    ∀ (ps qs : Bool → U → ℝ) (δsp Dexc : ℝ),
    (∀ j,SparseIntersectionData (if j then Hₖ else H₀) (ps j) (qs j) L δsp Dexc) →
    δsp+Dexc/(Fintype.card V:ℝ)+1/(Fintype.card U:ℝ)≤δ₀ →
    ∀ i : Bool → Fin (k+2),(∀ j,markedPositionType (i j)=j) →
    (∀ u u' : U,u≠u' → 2*β*(Fintype.card V:ℝ)^(k+2)≤
      (Fintype.card (CommonMarkedCycle tail head ktail khead (k+1) π b H₀ Hₖ u u'):ℝ)) →
    (∀ j,∀ Q : BipartiteFourCycle (if j then Hₖ else H₀),
      2*β*(Fintype.card V:ℝ)^(k+1)≤
      (Fintype.card (CanonicalCommonMarkedPath tail head ktail khead (k+1) π b H₀ Hₖ (i j)
        Q.val.1.1 Q.val.1.2 Q.val.2.1 Q.val.2.2):ℝ)) →
    ∀ ψ : MarkedWheel tail head ktail khead (k+1) π b H₀ Hₖ → ℝ,
    (∀ e,|markedWheelRimLoad ψ e-1|≤η₀) →
    (∀ j v u,|markedSpokeResidual ψ j v u|≤η₀) →
    (∀ W,bminus/(Fintype.card V:ℝ)^(k+1)≤ψ W ∧ ψ W≤bplus/(Fintype.card V:ℝ)^(k+1)) →
    ∀ (J₀ Jₖ : V → V → ℕ) (L₀ Lₖ : V → U → ℕ),
    (∀ x y,J₀ x y≤occurrenceMultiplicity tail head x y) →
    (∀ x y,Jₖ x y≤occurrenceMultiplicity ktail khead x y) →
    (∀ v u,L₀ v u≤relationMultiplicity H₀ v u) →
    (∀ v u,Lₖ v u≤relationMultiplicity Hₖ v u) →
    TypedMatrixBalanced (k+1)
      (occurrenceMultiplicity (fun e : {e // J₀ (tail e) (head e)=0}=>tail e.val) (fun e=>head e.val))
      (occurrenceMultiplicity (fun e : {e // Jₖ (ktail e) (khead e)=0}=>ktail e.val) (fun e=>khead e.val))
      (relationMultiplicity (fun v u=>H₀ v u ∧ L₀ v u=0))
      (relationMultiplicity (fun v u=>Hₖ v u ∧ Lₖ v u=0)) →
    (∀ v,(∑ x,(J₀ v x:ℝ))≤σ*Fintype.card V ∧ (∑ x,(J₀ x v:ℝ))≤σ*Fintype.card V ∧
      (∑ x,(Jₖ v x:ℝ))≤σ*Fintype.card V ∧ (∑ x,(Jₖ x v:ℝ))≤σ*Fintype.card V ∧
      (∑ u,(L₀ v u:ℝ))≤σ*Fintype.card V ∧ (∑ u,(Lₖ v u:ℝ))≤σ*Fintype.card V) →
    (∀ u,(∑ v,(L₀ v u:ℝ))≤σ*Fintype.card V ∧ (∑ v,(Lₖ v u:ℝ))≤σ*Fintype.card V) →
    ∃ M : Finset (MarkedWheel tail head ktail khead (k+1) π b H₀ Hₖ),
      (∀ W∈M,∀ Z∈M,W≠Z → Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z)) ∧
      (∀ x : V⊕U,((markedIncidentEdges tail head ktail khead π H₀ Hₖ false x \
        M.biUnion markedActiveResources).card : ℝ)≤γ*Fintype.card V) ∧
      (∀ x : V⊕U,((markedPhysicalIncidentEdges tail head ktail khead π H₀ Hₖ x \
        M.biUnion markedWheelPhysicalResources).card : ℝ)≤γ*Fintype.card V) := by
  obtain ⟨c₀,hc₀⟩ := marked_balanced_wheel_packing α p₀ hα hαmax hp₀ hp₀max
  refine ⟨max c₀ 4,?_⟩
  intro k hk β L bminus bplus ω hβ hL hbm hbp hω
  have hkm : 3≤k+1 := by omega
  let c : ℝ := (k:ℝ)+2
  have hc : 0<c := by dsimp only [c];positivity
  obtain ⟨ε,η₀,δ₀,hε,hη,hδ,hpacking⟩ := hc₀ k ((le_max_left _ _).trans hk) β L bminus bplus hβ hL hbm hbp
  refine ⟨ε/2,η₀/2,δ₀/2,by positivity,by positivity,by positivity,?_⟩
  intro γ hγ
  let σ := min (ε/2) (min (α*p₀^2/4) (min (α*p₀/32)
    (min (β/(8*c)) (min (η₀/(32*c^4*bplus)) (min (δ₀*ω/(12*(L^2+ω))) (γ/12))))))
  have hσ : 0<σ := by dsimp only [σ];positivity
  have hsε : σ≤ε/2 := min_le_left _ _
  have hs2 : σ≤α*p₀^2/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hsCut : σ≤α*p₀/32 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsCount : σ≤β/(8*c) := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsLoad : σ≤η₀/(32*c^4*bplus) := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hsData : σ≤δ₀*ω/(12*(L^2+ω)) := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hsγ : σ≤γ/12 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  refine ⟨σ,hσ,?_⟩
  intro b
  obtain ⟨N,hN⟩ := hpacking b (γ/2) (by positivity)
  refine ⟨max 1 N,?_⟩
  intro V E K U _ _ _ _ _ _ tail head ktail khead π hphys p D hp hpmax hn hDlo hDhi
    hdo hdi hdko hdki htwo hcut H₀ Hₖ hdisj hhub hωn huV ps qs δsp Dexc hdata hsmall i hipos
    hcommon hpaths ψ hRerr hSerr hψ J₀ Jₖ L₀ Lₖ hJ0 hJK hL0 hLK hbalance hV hU
  let n : ℝ := Fintype.card V
  have hnpos : 0<Fintype.card V := by omega
  have hnreal : 0<n := by change 0<(Fintype.card V:ℝ);exact_mod_cast hnpos
  have hu : 0<Fintype.card U := by
    have hh : 0<(Fintype.card U:ℝ) := (mul_pos hω hnreal).trans_le hωn
    exact_mod_cast hh
  let d := σ*n
  have hd : 0≤d := le_of_lt (mul_pos hσ hnreal)
  let PE : E → Prop := fun e=>J₀ (tail e) (head e)=0
  let PK : K → Prop := fun e=>Jₖ (ktail e) (khead e)=0
  let H₀' : V → U → Prop := fun v u=>H₀ v u ∧ L₀ v u=0
  let Hₖ' : V → U → Prop := fun v u=>Hₖ v u ∧ Lₖ v u=0
  letI : DecidablePred PE := fun e=>Classical.propDecidable (PE e)
  letI : DecidablePred PK := fun e=>Classical.propDecidable (PK e)
  letI : DecidableRel H₀' := fun v u=>Classical.propDecidable (H₀' v u)
  letI : DecidableRel Hₖ' := fun v u=>Classical.propDecidable (Hₖ' v u)
  have hH0 : ∀ v u,H₀' v u → H₀ v u := fun _ _ h=>h.1
  have hHK : ∀ v u,Hₖ' v u → Hₖ v u := fun _ _ h=>h.1
  obtain ⟨hinj,hkinj⟩ := markedPhysicalEdge_endpoint_injections tail head ktail khead π hphys
  have hEout (v : V) : (∑ e,if ¬PE e ∧ tail e=v then (1:ℝ) else 0)≤d := by
    have he := occurrence_matrix_deleted_degree tail head hinj J₀ hJ0 v
    have he' : (∑ e,if ¬PE e ∧ tail e=v then (1:ℝ) else 0)=∑ y,(J₀ v y:ℝ) := by
      convert he using 1 <;> congr!
    exact he'.le.trans (hV v).1
  have hEin (v : V) : (∑ e,if ¬PE e ∧ head e=v then (1:ℝ) else 0)≤d := by
    have he := occurrence_matrix_deleted_indegree tail head hinj J₀ hJ0 v
    have he' : (∑ e,if ¬PE e ∧ head e=v then (1:ℝ) else 0)=∑ y,(J₀ y v:ℝ) := by
      convert he using 1 <;> congr!
    exact he'.le.trans (hV v).2.1
  have hKout (v : V) : (∑ e,if ¬PK e ∧ ktail e=v then (1:ℝ) else 0)≤d := by
    have he := occurrence_matrix_deleted_degree ktail khead hkinj Jₖ hJK v
    have he' : (∑ e,if ¬PK e ∧ ktail e=v then (1:ℝ) else 0)=∑ y,(Jₖ v y:ℝ) := by
      convert he using 1 <;> congr!
    exact he'.le.trans (hV v).2.2.1
  have hKin (v : V) : (∑ e,if ¬PK e ∧ khead e=v then (1:ℝ) else 0)≤d := by
    have he := occurrence_matrix_deleted_indegree ktail khead hkinj Jₖ hJK v
    have he' : (∑ e,if ¬PK e ∧ khead e=v then (1:ℝ) else 0)=∑ y,(Jₖ y v:ℝ) := by
      convert he using 1 <;> congr!
    exact he'.le.trans (hV v).2.2.2.1
  have hH0row (v : V) : (∑ u,if H₀ v u ∧ ¬H₀' v u then (1:ℝ) else 0)≤d := by
    calc
      _ = ∑ u,(L₀ v u:ℝ) := by
        apply Finset.sum_congr rfl
        intro u _
        convert relation_matrix_deleted_entry H₀ L₀ hL0 v u using 1 <;> congr!
      _ ≤ d := (hV v).2.2.2.2.1
  have hHKrow (v : V) : (∑ u,if Hₖ v u ∧ ¬Hₖ' v u then (1:ℝ) else 0)≤d := by
    calc
      _ = ∑ u,(Lₖ v u:ℝ) := by
        apply Finset.sum_congr rfl
        intro u _
        convert relation_matrix_deleted_entry Hₖ Lₖ hLK v u using 1 <;> congr!
      _ ≤ d := (hV v).2.2.2.2.2
  have hH0col (u : U) : (∑ v,if H₀ v u ∧ ¬H₀' v u then (1:ℝ) else 0)≤d := by
    calc
      _ = ∑ v,(L₀ v u:ℝ) := by
        apply Finset.sum_congr rfl
        intro v _
        convert relation_matrix_deleted_entry H₀ L₀ hL0 v u using 1 <;> congr!
      _ ≤ d := (hU u).1
  have hHKcol (u : U) : (∑ v,if Hₖ v u ∧ ¬Hₖ' v u then (1:ℝ) else 0)≤d := by
    calc
      _ = ∑ v,(Lₖ v u:ℝ) := by
        apply Finset.sum_congr rfl
        intro v _
        convert relation_matrix_deleted_entry Hₖ Lₖ hLK v u using 1 <;> congr!
      _ ≤ d := (hU u).2
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
  have htwo' (x y : V) (hxy : x≠y) : α*p^2*n≤
      ((Finset.univ.filter (fun z=>(∃ e : {e // PE e},tail e.val=x ∧ head e.val=z) ∧
        (∃ e : {e // PE e},tail e.val=z ∧ head e.val=y))).card:ℝ) := by
    have hbase := htwo x y hxy
    have hloss := represented_two_step_deletion tail head PE x y d (by convert hEout x using 1 <;> congr!) (by convert hEin y using 1 <;> congr!)
    have hh := (abs_le.mp hloss).1
    change 2*α*p^2*n≤_ at hbase
    linarith only [hh,hbase,htwoCost]
  have hcutCost : d≤(α*p/16)*n := by
    have h1 := mul_le_mul_of_nonneg_right hsCut hnreal.le
    have h2 := mul_le_mul_of_nonneg_left hp (mul_nonneg hα.le hnreal.le)
    dsimp only [d]
    nlinarith only [h1,h2,mul_nonneg hσ.le hnreal.le]
  have hcut' (S T : Finset V)
      (hST : (1-2*min (α/16) (p/128))*n<(S.card:ℝ)+T.card) :
      (α*p/16)*n*min (S.card:ℝ) T.card≤
        ((Finset.univ.filter (fun e : {e // PE e}=>tail e.val∈S ∧ head e.val∈T)).card:ℝ) := by
    have hbase := hcut S T hST
    have hloss := occurrence_matrix_cut_deletion tail head hinj J₀ hJ0 d
      (fun v=>(hV v).1) (fun v=>(hV v).2.1) S T
    have hs : 0≤min (S.card:ℝ) T.card := by positivity
    have hh := mul_le_mul_of_nonneg_right hcutCost hs
    change 2*(α*p/16)*n*min (S.card:ℝ) T.card≤_ at hbase
    have hi : (α*p/16)*n*min (S.card:ℝ) T.card≤
        ((Finset.univ.filter (fun e : E=>tail e∈S ∧ head e∈T)).card:ℝ)-d*min (S.card:ℝ) T.card := by
      linarith only [hbase,hh]
    convert (hi.trans (by convert hloss using 1 <;> congr!)) using 1 <;> congr!
  have hcountCost : 4*c*d≤β*n := by
    have hs := (le_div_iff₀ (by positivity : 0<8*c)).mp hsCount
    have hh := mul_le_mul_of_nonneg_right hs hnreal.le
    have hnon : 0≤c*d := mul_nonneg hc.le hd
    dsimp only [d] at hnon ⊢
    nlinarith only [hh,hnon]
  have hcEq : ((k+1:ℕ):ℝ)+1=c := by dsimp only [c];push_cast;ring
  have hhub' := marked_hub_count_restriction PE PK hH0 hHK β d
    (by rw [hcEq];nlinarith only [hcountCost,mul_nonneg hc.le hd]) (by convert hH0row using 1 <;> congr!) (by convert hHKrow using 1 <;> congr!) hhub
  have hcommon' (u u' : U) (hne : u≠u') : β*n^(k+2)≤
      (Fintype.card (CommonMarkedCycle (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
        (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) (k+1) π b H₀' Hₖ' u u'):ℝ) := by
    have hh := marked_common_cycle_count_restriction (by omega : 1≤k+1) PE PK β d
      (by rw [hcEq];nlinarith only [hcountCost,mul_nonneg hc.le hd]) (by convert hEout using 1 <;> congr!) (by convert hKout using 1 <;> congr!) (by convert hH0col using 1 <;> congr!) (by convert hHKcol using 1 <;> congr!) u u' (hcommon u u' hne)
    convert hh using 1 <;> congr!
  have htyped (j : Bool) (v : V) (u : U) :
      (if j then Hₖ' else H₀') v u → (if j then Hₖ else H₀) v u := by
    cases j
    · exact hH0 v u
    · exact hHK v u
  have hpaths' (j : Bool) (Q : BipartiteFourCycle (if j then Hₖ' else H₀')) :
      β*n^(k+1)≤
      (Fintype.card (MarkedReplacementPair (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
        (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) (k+1) π b H₀' Hₖ' (i j)
        Q.val.1.1 Q.val.1.2 Q.val.2.1 Q.val.2.2):ℝ) := by
    let Qp : BipartiteFourCycle (if j then Hₖ else H₀) :=
      ⟨Q.val,Q.property.1,Q.property.2.1,htyped j _ _ Q.property.2.2.1,
        htyped j _ _ Q.property.2.2.2.1,htyped j _ _ Q.property.2.2.2.2.1,
        htyped j _ _ Q.property.2.2.2.2.2⟩
    have hroot : (if markedPositionType (i j) then Hₖ' Q.val.1.1 Q.val.2.1 else H₀' Q.val.1.1 Q.val.2.1) ∧
        (if markedPositionType (i j) then Hₖ' Q.val.1.1 Q.val.2.2 else H₀' Q.val.1.1 Q.val.2.2) ∧
        (if markedPositionType (i j) then Hₖ' Q.val.1.2 Q.val.2.1 else H₀' Q.val.1.2 Q.val.2.1) ∧
        (if markedPositionType (i j) then Hₖ' Q.val.1.2 Q.val.2.2 else H₀' Q.val.1.2 Q.val.2.2) := by
      rw [hipos j]
      simpa only [ite_apply] using
        And.intro Q.property.2.2.1 (And.intro Q.property.2.2.2.2.2
          (And.intro Q.property.2.2.2.1 Q.property.2.2.2.2.1))
    have hh := marked_replacement_pair_count_restriction (by omega : 1≤k+1) PE PK β d
      (by rw [hcEq];exact hcountCost) (by convert hEout using 1 <;> congr!) (by convert hEin using 1 <;> congr!) (by convert hKout using 1 <;> congr!) (by convert hKin using 1 <;> congr!) (by convert hH0col using 1 <;> congr!) (by convert hHKcol using 1 <;> congr!)
      (i j) Q.val.1.1 Q.val.1.2 Q.val.2.1 Q.val.2.2 hroot (hpaths j Qp)
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
  obtain ⟨hbdir,hbK,hbout,hbcol⟩ := typed_matrix_balanced_occurrence_degrees (k+1)
    (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
    (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) H₀' Hₖ' (by convert hbalance using 1 <;> congr!)
  obtain ⟨M,hM,haux,hphysical⟩ := hN V {e // PE e} {e // PK e} U
    (fun e=>tail e.val) (fun e=>head e.val) (fun e=>ktail e.val) (fun e=>khead e.val) π hphys'
    p D hp hpmax ((le_max_right _ _).trans hn) hDlo hDhi hd0 hdi0 hdk0 hdki0 (by convert htwo' using 1 <;> congr!) (by convert hcut' using 1 <;> congr!) H₀' Hₖ'
    hdisj' hhub' hbdir hbK hbout (by simpa only [Nat.cast_add,Nat.cast_one] using hbcol)
    hu huV ps qs (δsp+ρ) Dexc hdata' hsmall' i hipos hcommon' hpaths' η₀ hη.le le_rfl ψ' hR'' hS'' hψ'
  obtain ⟨hM',haux',hphysical'⟩ := marked_packing_transport_bounds PE PK hH0 hHK hphys M hM ((γ/2)*n) d hd
    (by convert haux using 1 <;> congr!) (by convert hphysical using 1 <;> congr!) (by convert hEout using 1 <;> congr!) (by convert hEin using 1 <;> congr!) (by convert hKout using 1 <;> congr!) (by convert hKin using 1 <;> congr!) (by convert hH0row using 1 <;> congr!) (by convert hHKrow using 1 <;> congr!) (by convert hH0col using 1 <;> congr!) (by convert hHKcol using 1 <;> congr!)
  refine ⟨M.image (markedWheelToLarger PE PK hH0 hHK),hM',?_,?_⟩
  · intro x
    have hh := haux' x
    have hcost := mul_le_mul_of_nonneg_right hsγ hnreal.le
    change _≤γ*n
    dsimp only [d] at hh
    linarith only [hh,hcost]
  · intro x
    have hh := hphysical' x
    have hcost := mul_le_mul_of_nonneg_right hsγ hnreal.le
    change _≤γ*n
    dsimp only [d] at hh
    linarith only [hh,hcost]

end Oberwolfach
