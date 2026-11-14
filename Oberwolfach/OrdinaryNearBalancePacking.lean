module

public import Oberwolfach.SparseOrdinaryCorrection
public import Oberwolfach.IsolatorDeletionStability
public import Oberwolfach.TransferDeletionStability
public import Oberwolfach.PositiveOrdinaryWheelWeights
public import Oberwolfach.OrdinaryWheelPacking
public import Oberwolfach.OrdinaryPackingTransport

@[expose] public section

/-! Ordinary wheel packing from near balance and supplied positive weights.
The weight tolerance precedes the requested uncovered-degree tolerance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_near_balance_wheel_packing (r : ℕ) (hr : 3≤r) (α : ℝ) (hα : 0<α) :
    ∃ N : ℕ,∀ k : ℕ,N≤k → ∀ ω β bminus bplus h δ : ℝ,
      0<ω → 0<β → 0<bminus → 0<bplus → 0<h → 0<δ → δ<1/4 →
      ∃ εstar : ℝ,0<εstar ∧ ∀ γ : ℝ,0<γ → ∃ η : ℝ,0<η ∧ ∃ n₀ : ℕ,
      ∀ (V U : Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
      n₀≤Fintype.card V → ω*Fintype.card V≤Fintype.card U → Fintype.card U≤Fintype.card V →
      ∀ (P Q F : SimpleGraph V) (H : V → U → Prop) (A : V → V → ℕ),
      Q≤P\F → (∀ x y,A x y+A y x=if Q.Adj x y then 1 else 0) →
      BipartiteLargeCut A δ h → BipartiteLargeCut (fun v u=>if H v u then 1 else 0) δ h →
      (∀ v,β*Fintype.card V≤((Finset.univ.filter (H v)).card:ℝ)) →
      (∀ v,|(Q.degree v:ℝ)-2*(Finset.univ.filter (H v)).card|≤η*Fintype.card V) →
      (∀ x y,Q.Adj x y → β*(Fintype.card V:ℝ)^(k-1)≤
        (Fintype.card (OrdinaryIsolatorConfiguration P Q F H k (max (1/2) (cycleThreshold r)) (α/4) x y):ℝ)) →
      (∀ v (i j : {u // H v u}),i.val≠j.val → β*(Fintype.card V:ℝ)^(r^2)≤
        (Fintype.card (OrdinaryTransferConfiguration hr Q F H v i.val j.val):ℝ)) →
      ∀ w : OrdinaryWheel Q F H r → ℝ,
      (∀ W,bminus/(Fintype.card V:ℝ)^(r-1)≤w W ∧ w W≤bplus/(Fintype.card V:ℝ)^(r-1)) →
      (∀ x y,Q.Adj x y → |ordinaryRimLoad w x y-1|≤εstar) →
      (∀ v u,H v u → |ordinarySpokeLoad w v u-1|≤εstar) →
      ∃ M : Finset (OrdinaryWheel Q F H r),
      (∀ W∈M,∀ Z∈M,W≠Z → Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z)) ∧
      ∀ x : V⊕U,((ordinaryIncidentEdges Q H x \ M.biUnion ordinaryActiveResources).card:ℝ)≤
        γ*Fintype.card V := by
  classical
  obtain ⟨N,hN⟩ := positive_ordinary_wheel_weights r hr α hα
  refine ⟨max N (r+2),?_⟩
  intro k hk ω β bminus bplus h δ hω hβ hbm hbp hh hδ hδsmall
  have hkN : N≤k := (le_max_left _ _).trans hk
  have hk4 : 4≤k := by have ht := (le_max_right N (r+2)).trans hk;omega
  let θ := max (1/2) (cycleThreshold r)
  obtain ⟨εW,hεW,hweights⟩ := hN k hkN θ (β/2) bminus bplus le_rfl (by positivity) hbm hbp
  refine ⟨εW/4,by positivity,?_⟩
  intro γ hγ
  have hrR : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  let ξ := min (min (h/100) (γ/20))
    (min (β/160) (min (β/(100*(r:ℝ)^4)) (εW/(320*(r:ℝ)^4*bplus))))
  have hξ : 0<ξ := by dsimp [ξ];positivity
  have hξh : ξ≤h/100 := (min_le_left _ _).trans (min_le_left _ _)
  have hξγ : 10*ξ≤γ/2 := by
    have ht : ξ≤γ/20 := (min_le_left _ _).trans (min_le_right _ _)
    linarith
  have hξβ : 80*ξ≤β/2 := by
    have ht : ξ≤β/160 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hξT : 50*(r:ℝ)^4*ξ≤β/2 := by
    have ht : ξ≤β/(100*(r:ℝ)^4) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hb := (le_div_iff₀ (show 0<100*(r:ℝ)^4 by positivity)).mp ht
    nlinarith
  have hξL : 80*(r:ℝ)^4*bplus*ξ≤εW/4 := by
    have ht : ξ≤εW/(320*(r:ℝ)^4*bplus) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hb := (le_div_iff₀ (show 0<320*(r:ℝ)^4*bplus by positivity)).mp ht
    nlinarith
  obtain ⟨η,hη,Ncorr,hcorr⟩ := sparse_ordinary_degree_correction r hr ω h δ ξ hω hh hδ hδsmall hξ hξh
  obtain ⟨Npack,hpack⟩ := ordinary_wheel_packing_bounded_hubs r hr (bplus+bminus/2) (γ/2)
    (by positivity) (by positivity)
  refine ⟨η,hη,max 1 (max Ncorr Npack),?_⟩
  intro V U _ _ _ _ hn hωn hu P Q F H A hQP hA hcutA hcutH hH hbal hI hT w hw hR hS
  let n := Fintype.card V
  have hn1 : 1≤n := (le_max_left _ _).trans hn
  have hn0 : 0<n := by omega
  have hnR : (0:ℝ)<n := by exact_mod_cast hn0
  have hnc : Ncorr≤n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnp : Npack≤n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  obtain ⟨D,E,hDsub,hEsub,hbalance,_hdiv,hdelV,hdelU⟩ :=
    hcorr η hη.le le_rfl V U hnc hωn hu Q ⊥ H (fun _ _=>False) A
      (by simpa using hA) hcutA (by simpa using hcutH) hbal
  have hEQ : D≤Q := by simpa using hDsub
  have hEH : ∀ v u,E v u → H v u := fun v u he=>(hEsub v u he).1
  let Q' := Q\D
  let H' : V → U → Prop := fun v u=>H v u ∧ ¬E v u
  let d := 10*ξ*(n:ℝ)
  have hd : 0≤d := by dsimp [d];positivity
  have hD (v : V) : (D.degree v:ℝ)≤d := by
    have ht := hdelV v
    have hp : (0:ℝ)≤(Finset.univ.filter (E v)).card := by positivity
    change _≤d at ht
    linarith
  have hEv (v : V) : ((Finset.univ.filter (E v)).card:ℝ)≤d := by
    have ht := hdelV v
    have hp : (0:ℝ)≤D.degree v := by positivity
    change _≤d at ht
    linarith
  have hEout (v : V) : (∑ u,bipAdj E v u)≤d := by
    simpa [bipAdj,Finset.sum_boole] using hEv v
  have hEin (u : U) : (∑ v,bipAdj E v u)≤d := by
    simpa [bipAdj,Finset.sum_boole,d,n] using hdelU u
  have hH' (v : V) : (β/2)*(n:ℝ)≤((Finset.univ.filter (H' v)).card:ℝ) := by
    have heq := relation_deleted_row_degree H E hEH v
    have hle : (Finset.univ.filter (E v)).card≤(Finset.univ.filter (H v)).card := by
      apply Finset.card_le_card
      intro u hu
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at *
      exact hEH v u hu
    have heqR : ((Finset.univ.filter (H' v)).card:ℝ)=
        (Finset.univ.filter (H v)).card-(Finset.univ.filter (E v)).card := by
      rw [show (Finset.univ.filter (H' v)).card=_ from heq,Nat.cast_sub hle]
    have hbound := hEv v
    have hsmall : d≤(β/2)*(n:ℝ) := by
      dsimp [d]
      apply mul_le_mul_of_nonneg_right _ hnR.le
      linarith
    have hbase := hH v
    change β*(n:ℝ)≤_ at hbase
    linarith
  have hI' (x y : V) (hxy : Q'.Adj x y) : (β/2)*(n:ℝ)^(k-1)≤
      (Fintype.card (OrdinaryIsolatorConfiguration P Q' F H' k θ (α/4) x y):ℝ) := by
    have hxyQ : Q.Adj x y := hxy.1
    have hloss := ordinary_isolator_deletion_stability (P:=P) (Q:=Q) (F:=F) (H:=H)
      (k:=k) (θ:=θ) (α:=α/4) hxyQ.ne hk4 hn0 hu D E d hD hEout hEin hxy.2
    have hpow : (n:ℝ)^(k-1)=(n:ℝ)^(k-2)*(n:ℝ) := by
      rw [← pow_succ];congr 1;omega
    have hsmall : 8*d*(n:ℝ)^(k-2)≤(β/2)*(n:ℝ)^(k-1) := by
      rw [hpow]
      dsimp [d]
      nlinarith [mul_le_mul_of_nonneg_right hξβ (show 0≤(n:ℝ)^(k-2)*(n:ℝ) by positivity)]
    have hbase := hI x y hxyQ
    change β*(n:ℝ)^(k-1)≤_ at hbase
    change (_:ℝ)-(Fintype.card (OrdinaryIsolatorConfiguration P Q' F H' k θ (α/4) x y):ℝ)≤_ at hloss
    nlinarith
  have hT' (v : V) (i j : {u // H' v u}) (hne : i.val≠j.val) :
      (β/2)*(n:ℝ)^(r^2)≤(Fintype.card (OrdinaryTransferConfiguration hr Q' F H' v i.val j.val):ℝ) := by
    have hloss := ordinary_transfer_deletion_stability (hr:=hr) (Q:=Q) (F:=F) (H:=H)
      (v:=v) (u:=i.val) (u':=j.val) D E d hd hn0 hD hEin ⟨i.property.2,j.property.2⟩
    have hpow : (n:ℝ)^(r^2)=(n:ℝ)^(r^2-1)*(n:ℝ) := by
      rw [← pow_succ];congr 1
      have hp : 0<r^2 := pow_pos (show 0<r by omega) _
      omega
    have hsmall : 5*(r:ℝ)^4*d*(n:ℝ)^(r^2-1)≤(β/2)*(n:ℝ)^(r^2) := by
      rw [hpow]
      dsimp [d]
      nlinarith [mul_le_mul_of_nonneg_right hξT (show 0≤(n:ℝ)^(r^2-1)*(n:ℝ) by positivity)]
    have hbase := hT v ⟨i.val,i.property.1⟩ ⟨j.val,j.property.1⟩ hne
    change β*(n:ℝ)^(r^2)≤_ at hbase
    change (_:ℝ)-(Fintype.card (OrdinaryTransferConfiguration hr Q' F H' v i.val j.val):ℝ)≤_ at hloss
    nlinarith
  let incl := ordinaryWheelToLarger (F:=F) (r:=r) (sdiff_le : Q'≤Q)
    (fun v u (he : H' v u)=>he.1)
  let w' : OrdinaryWheel Q' F H' r → ℝ := fun W=>w (incl W)
  have hw0 (W : OrdinaryWheel Q F H r) : 0≤w W ∧ w W≤bplus/(n:ℝ)^(r-1) :=
    ⟨(by positivity : 0≤bminus/(n:ℝ)^(r-1)).trans (hw W).1,(hw W).2⟩
  have hR' (x y : V) (hxy : Q'.Adj x y) : |ordinaryRimLoad w' x y-1|≤εW := by
    have hstab := ordinary_restricted_rim_load_stability Q F D H E r (by omega) hn0 hu w bplus d
      hbp.le hd hw0 hD hEout hEin x y hxy
    change |ordinaryRimLoad w' x y-ordinaryRimLoad w x y|≤8*(r:ℝ)^4*bplus*d/(n:ℝ) at hstab
    have heq : 8*(r:ℝ)^4*bplus*d/(n:ℝ)=80*(r:ℝ)^4*bplus*ξ := by
      dsimp [d];field_simp;ring
    rw [heq] at hstab
    have hbase := hR x y hxy.1
    have htri := abs_sub_le (ordinaryRimLoad w' x y) (ordinaryRimLoad w x y) 1
    linarith
  have hS' (v : V) (u : U) (hvu : H' v u) : |ordinarySpokeLoad w' v u-1|≤εW := by
    have hstab := ordinary_restricted_spoke_load_stability Q F D H E r (by omega) hn0 hu w bplus d
      hbp.le hd hw0 hD hEout hEin v u hvu
    change |ordinarySpokeLoad w' v u-ordinarySpokeLoad w v u|≤4*(r:ℝ)^4*bplus*d/(n:ℝ) at hstab
    have heq : 4*(r:ℝ)^4*bplus*d/(n:ℝ)=40*(r:ℝ)^4*bplus*ξ := by
      dsimp [d];field_simp;ring
    rw [heq] at hstab
    have hbase := hS v u hvu.1
    have htri := abs_sub_le (ordinarySpokeLoad w' v u) (ordinarySpokeLoad w v u) 1
    linarith
  obtain ⟨wexact,hexR,hexS,hexBound⟩ := hweights V U hn0 hu P Q' F H'
    (sdiff_le.trans hQP)
    (by intro v;convert hbalance v using 1 <;> congr!)
    (by intro v;simpa only [H',n,Finset.filter_congr_decidable] using hH' v) hI' hT' εW hεW.le le_rfl w'
    (fun W=>hw (incl W)) hR' hS'
  obtain ⟨M,hM,hleft⟩ := hpack V U hnp hu Q' F H' wexact
    (fun W=>⟨(by positivity : 0≤(bminus/2)/(n:ℝ)^(r-1)).trans (hexBound W).1,(hexBound W).2⟩)
    hexR hexS
  obtain ⟨hM',hresources⟩ := ordinary_packing_transport (sdiff_le : Q'≤Q)
    (fun v u (he : H' v u)=>he.1) M hM
  refine ⟨M.image incl,hM',?_⟩
  intro x
  rw [ordinary_leftover_card_physical]
  change (M.image incl).biUnion ordinaryWheelResources=M.biUnion ordinaryWheelResources at hresources
  rw [hresources]
  have hcard := finset_uncovered_le_after_deletion (ordinaryPhysicalIncidentEdges Q H x)
    (ordinaryPhysicalIncidentEdges D E x) (M.biUnion ordinaryWheelResources)
  rw [← ordinaryPhysicalIncidentEdges_delete] at hcard
  have hcardR := (Nat.cast_le (α:=ℝ)).mpr hcard
  rw [Nat.cast_add] at hcardR
  have hsmall := hleft x
  rw [ordinary_leftover_card_physical] at hsmall
  have hdeleted : ((ordinaryPhysicalIncidentEdges D E x).card:ℝ)≤d := by
    cases x with
    | inl v =>
      rw [ordinaryPhysicalIncidentEdges_rim_card,Nat.cast_add]
      exact hdelV v
    | inr u =>
      rw [ordinaryPhysicalIncidentEdges_hub_card]
      exact hdelU u
  have hdγ : d≤(γ/2)*(n:ℝ) := mul_le_mul_of_nonneg_right hξγ hnR.le
  change _≤(γ/2)*(n:ℝ) at hsmall
  change _≤γ*(n:ℝ)
  linarith

end Oberwolfach
