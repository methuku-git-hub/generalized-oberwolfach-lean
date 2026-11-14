module

public import Oberwolfach.MarkedRimCorrection
public import Oberwolfach.MarkedWheelCorrection

@[expose] public section

/-! Positive marked wheel weights in the canonical representation. The
rim correction is supplied by the proved capacity theorem; both spoke
corrections are constructed on the actual counted cycle families. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
universe u v w z
attribute [local instance] Classical.propDecidable

theorem positive_marked_wheel_weights_uniform_parameters (α p₀ : ℝ)
    (hα : 0<α) (hαmax : α≤1) (hp₀ : 0<p₀) (hp₀max : p₀≤1/2) :
    ∃ c₀ : ℕ,∀ k : ℕ,c₀≤k+2 → ∀ β L bminus bplus : ℝ,0<β → 1≤L → 0<bminus → 0<bplus →
    ∃ ε η₀ δ₀ A : ℝ,0<ε ∧ 0<η₀ ∧ 0<δ₀ ∧ 0<A ∧
    ∀ b : ℕ,∃ n₀ : ℕ,
    ∀ (V : Type u) (E : Type v) (K : Type w) (U : Type z)
      [Fintype V] [Fintype E] [Fintype K] [Fintype U] [DecidableEq V] [DecidableEq U],
    ∀ (tail head : E → V) (ktail khead : K → V) (π : Equiv.Perm V),
    Function.Injective (markedPhysicalEdge tail head ktail khead π) →
    ∀ (p D : ℝ),p₀≤p → p≤1/2 → n₀≤Fintype.card V →
    (Fintype.card V:ℝ)/2≤D → D≤2*Fintype.card V →
    (∀ x,|occurrenceDegree tail x-p*D|≤ε*Fintype.card V) →
    (∀ x,|occurrenceDegree head x-p*D|≤ε*Fintype.card V) →
    (∀ x,|occurrenceDegree ktail x-p*D/(k+1:ℝ)|≤ε*Fintype.card V) →
    (∀ x,|occurrenceDegree khead x-p*D/(k+1:ℝ)|≤ε*Fintype.card V) →
    (∀ x y,x≠y → α*p^2*Fintype.card V≤
      ((Finset.univ.filter (fun z => (∃ e,tail e=x ∧ head e=z) ∧ (∃ e,tail e=z ∧ head e=y))).card:ℝ)) →
    (∀ S T : Finset V,(1-2*min (α/16) (p/128))*Fintype.card V<(S.card:ℝ)+T.card →
      (α*p/16)*Fintype.card V*min (S.card:ℝ) T.card≤
      ((Finset.univ.filter (fun e => tail e∈S ∧ head e∈T)).card:ℝ)) →
    ∀ H₀ Hₖ : V → U → Prop,
    (∀ C' : MarkedCycleTuple tail head ktail khead (k+1) π b,
      β*Fintype.card V≤(Fintype.card {u // MarkedHubCompatible H₀ Hₖ C'.val u}:ℝ)) →
    (∀ v,occurrenceDegree (Sum.elim tail ktail) v=occurrenceDegree (Sum.elim head khead) v) →
    (∀ v,occurrenceDegree khead v=∑ u,if Hₖ v u then (1:ℝ) else 0) →
    (∀ v,occurrenceDegree (Sum.elim tail ktail) v=
      (∑ u,if H₀ v u then (1:ℝ) else 0)+(∑ u,if Hₖ v u then (1:ℝ) else 0)) →
    (∀ u,(∑ v,if H₀ v u then (1:ℝ) else 0)=(k+1:ℝ)*(∑ v,if Hₖ v u then (1:ℝ) else 0)) →
    0<Fintype.card U →
    ∀ (ps qs : Bool → U → ℝ) (δsp Dexc : ℝ),
    (∀ j,SparseIntersectionData (if j then Hₖ else H₀) (ps j) (qs j) L δsp Dexc) →
    δsp+Dexc/(Fintype.card V:ℝ)+1/(Fintype.card U:ℝ)≤δ₀ →
    ∀ i : Bool → Fin (k+2),(∀ j,markedPositionType (i j)=j) →
    (∀ u u' : U,u≠u' → β*(Fintype.card V:ℝ)^(k+2)≤
      (Fintype.card (CommonMarkedCycle tail head ktail khead (k+1) π b H₀ Hₖ u u'):ℝ)) →
    (∀ j,∀ Q : BipartiteFourCycle (if j then Hₖ else H₀),
      β*(Fintype.card V:ℝ)^(k+1)≤
      (Fintype.card (MarkedReplacementPair tail head ktail khead (k+1) π b H₀ Hₖ (i j)
        Q.val.1.1 Q.val.1.2 Q.val.2.1 Q.val.2.2):ℝ)) →
    ∀ η : ℝ,0≤η → η≤η₀ →
    ∀ ψ : MarkedWheel tail head ktail khead (k+1) π b H₀ Hₖ → ℝ,
    (∀ e,|markedWheelRimLoad ψ e-1|≤η) →
    (∀ j v u,|markedSpokeResidual ψ j v u|≤η) →
    (∀ W,bminus/(Fintype.card V:ℝ)^(k+1)≤ψ W ∧ ψ W≤bplus/(Fintype.card V:ℝ)^(k+1)) →
    ∃ w : MarkedWheel tail head ktail khead (k+1) π b H₀ Hₖ → ℝ,
      (∀ e,markedWheelRimLoad w e=1) ∧
      (∀ j v u,markedWheelSpokeLoad w j v u=if (if j then Hₖ v u else H₀ v u) then 1 else 0) ∧
      (∀ W,(bminus/2)/(Fintype.card V:ℝ)^(k+1)≤w W ∧ w W≤A/(Fintype.card V:ℝ)^(k+1)) := by
  obtain ⟨c₀,hc₀⟩ := marked_rim_correction_uniform_parameters.{u,v,w,z} α p₀ hα hαmax hp₀ hp₀max
  refine ⟨c₀,?_⟩
  intro k hk β L bminus bplus hβ hL hbm hbp
  obtain ⟨ε,C,hε,hC,hcorr⟩ := hc₀ k hk β hβ
  let B := markedWheelCorrectionConstant (k+1) β L C
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hsp : 0≤markedSpokeCorrectionConstant (k+1) β L := by
    unfold markedSpokeCorrectionConstant
    positivity
  have hB : 0<B := by
    dsimp only [B,markedWheelCorrectionConstant]
    simp only [Nat.cast_add,Nat.cast_one]
    have hh : 0≤markedSpokeCorrectionConstant (k+1) β L*(1+(k+1+1)*C) := by positivity
    linarith
  let η₀ := min (1/2:ℝ) (bminus/(2*B))
  refine ⟨ε,η₀,1/(200*L^6),bplus+bminus/2,hε,by dsimp only [η₀];positivity,by positivity,by positivity,?_⟩
  intro b
  obtain ⟨n₀,hn₀⟩ := hcorr b
  refine ⟨max 1 n₀,?_⟩
  intro V E K U _ _ _ _ _ _ tail head ktail khead π hphys p D hp hpmax hn hDlo hDhi hdo hdi hdko hdki htwo hcut
    H₀ Hₖ hhub hdir hK hout hcol hu ps qs δsp Dexc hdata hsmall i hipos hcommon hpaths η hη hη₀ ψ hRerr hSerr hψ
  have hnpos : 0<Fintype.card V := (show 0<max 1 n₀ by omega).trans_le hn
  have hηmax : η<1 := lt_of_le_of_lt (hη₀.trans (min_le_left _ _)) (by norm_num)
  obtain ⟨R,hR,hRb,hRsp⟩ := hn₀ V E K U tail head ktail khead π hphys p D hp hpmax
    ((le_max_right _ _).trans hn) hDlo hDhi hdo hdi hdko hdki htwo hcut H₀ Hₖ hhub hdir hK hout hcol
    η hη hηmax ψ hRerr
  obtain ⟨hinj,hkinj⟩ := markedPhysicalEdge_endpoint_injections tail head ktail khead π hphys
  obtain ⟨w,hwR,hwS,hwb⟩ := marked_wheel_correction β η L δsp Dexc C hβ hη hC.le hnpos hu
    ps qs hdata hsmall i hipos hcommon hpaths hinj hkinj hK hout
    (by simpa only [Nat.cast_add,Nat.cast_one] using hcol) ψ R hR hRb
    (by simpa only [Nat.cast_add,Nat.cast_one,show (k:ℝ)+1+1=k+2 by ring] using hRsp) hSerr
  have htol : B*η≤bminus/2 := by
    have hh := (le_div_iff₀ (show 0<2*B by positivity)).mp (hη₀.trans (min_le_right _ _))
    nlinarith
  refine ⟨w,hwR,hwS,?_⟩
  intro W
  have hdiff : |w W-ψ W|≤(bminus/2)/(Fintype.card V:ℝ)^(k+1) :=
    (hwb W).trans (div_le_div_of_nonneg_right htol (by positivity))
  have hh := abs_le.mp hdiff
  have hlo := (hψ W).1
  have hhi := (hψ W).2
  constructor
  · have he : bminus/(Fintype.card V:ℝ)^(k+1)=2*((bminus/2)/(Fintype.card V:ℝ)^(k+1)) := by ring
    linarith
  · rw [add_div]
    linarith

theorem positive_marked_wheel_weights_uniform_length (α p₀ β L bminus bplus : ℝ)
    (hα : 0<α) (hαmax : α≤1) (hp₀ : 0<p₀) (hp₀max : p₀≤1/2) (hβ : 0<β)
    (hL : 1≤L) (hbm : 0<bminus) (hbp : 0<bplus) :
    ∃ c₀ : ℕ,∀ k : ℕ,c₀≤k+2 →
    ∃ ε η₀ δ₀ A : ℝ,0<ε ∧ 0<η₀ ∧ 0<δ₀ ∧ 0<A ∧
    ∀ b : ℕ,∃ n₀ : ℕ,
    ∀ (V : Type u) (E : Type v) (K : Type w) (U : Type z)
      [Fintype V] [Fintype E] [Fintype K] [Fintype U] [DecidableEq V] [DecidableEq U],
    ∀ (tail head : E → V) (ktail khead : K → V) (π : Equiv.Perm V),
    Function.Injective (markedPhysicalEdge tail head ktail khead π) →
    ∀ (p D : ℝ),p₀≤p → p≤1/2 → n₀≤Fintype.card V →
    (Fintype.card V:ℝ)/2≤D → D≤2*Fintype.card V →
    (∀ x,|occurrenceDegree tail x-p*D|≤ε*Fintype.card V) →
    (∀ x,|occurrenceDegree head x-p*D|≤ε*Fintype.card V) →
    (∀ x,|occurrenceDegree ktail x-p*D/(k+1:ℝ)|≤ε*Fintype.card V) →
    (∀ x,|occurrenceDegree khead x-p*D/(k+1:ℝ)|≤ε*Fintype.card V) →
    (∀ x y,x≠y → α*p^2*Fintype.card V≤
      ((Finset.univ.filter (fun z => (∃ e,tail e=x ∧ head e=z) ∧ (∃ e,tail e=z ∧ head e=y))).card:ℝ)) →
    (∀ S T : Finset V,(1-2*min (α/16) (p/128))*Fintype.card V<(S.card:ℝ)+T.card →
      (α*p/16)*Fintype.card V*min (S.card:ℝ) T.card≤
      ((Finset.univ.filter (fun e => tail e∈S ∧ head e∈T)).card:ℝ)) →
    ∀ H₀ Hₖ : V → U → Prop,
    (∀ C' : MarkedCycleTuple tail head ktail khead (k+1) π b,
      β*Fintype.card V≤(Fintype.card {u // MarkedHubCompatible H₀ Hₖ C'.val u}:ℝ)) →
    (∀ v,occurrenceDegree (Sum.elim tail ktail) v=occurrenceDegree (Sum.elim head khead) v) →
    (∀ v,occurrenceDegree khead v=∑ u,if Hₖ v u then (1:ℝ) else 0) →
    (∀ v,occurrenceDegree (Sum.elim tail ktail) v=
      (∑ u,if H₀ v u then (1:ℝ) else 0)+(∑ u,if Hₖ v u then (1:ℝ) else 0)) →
    (∀ u,(∑ v,if H₀ v u then (1:ℝ) else 0)=(k+1:ℝ)*(∑ v,if Hₖ v u then (1:ℝ) else 0)) →
    0<Fintype.card U →
    ∀ (ps qs : Bool → U → ℝ) (δsp Dexc : ℝ),
    (∀ j,SparseIntersectionData (if j then Hₖ else H₀) (ps j) (qs j) L δsp Dexc) →
    δsp+Dexc/(Fintype.card V:ℝ)+1/(Fintype.card U:ℝ)≤δ₀ →
    ∀ i : Bool → Fin (k+2),(∀ j,markedPositionType (i j)=j) →
    (∀ u u' : U,u≠u' → β*(Fintype.card V:ℝ)^(k+2)≤
      (Fintype.card (CommonMarkedCycle tail head ktail khead (k+1) π b H₀ Hₖ u u'):ℝ)) →
    (∀ j,∀ Q : BipartiteFourCycle (if j then Hₖ else H₀),
      β*(Fintype.card V:ℝ)^(k+1)≤
      (Fintype.card (MarkedReplacementPair tail head ktail khead (k+1) π b H₀ Hₖ (i j)
        Q.val.1.1 Q.val.1.2 Q.val.2.1 Q.val.2.2):ℝ)) →
    ∀ η : ℝ,0≤η → η≤η₀ →
    ∀ ψ : MarkedWheel tail head ktail khead (k+1) π b H₀ Hₖ → ℝ,
    (∀ e,|markedWheelRimLoad ψ e-1|≤η) →
    (∀ j v u,|markedSpokeResidual ψ j v u|≤η) →
    (∀ W,bminus/(Fintype.card V:ℝ)^(k+1)≤ψ W ∧ ψ W≤bplus/(Fintype.card V:ℝ)^(k+1)) →
    ∃ w : MarkedWheel tail head ktail khead (k+1) π b H₀ Hₖ → ℝ,
      (∀ e,markedWheelRimLoad w e=1) ∧
      (∀ j v u,markedWheelSpokeLoad w j v u=if (if j then Hₖ v u else H₀ v u) then 1 else 0) ∧
      (∀ W,(bminus/2)/(Fintype.card V:ℝ)^(k+1)≤w W ∧ w W≤A/(Fintype.card V:ℝ)^(k+1)) := by
  obtain ⟨c₀,hc₀⟩ := positive_marked_wheel_weights_uniform_parameters.{u,v,w,z} α p₀ hα hαmax hp₀ hp₀max
  exact ⟨c₀,fun k hk=>hc₀ k hk β L bminus bplus hβ hL hbm hbp⟩

end Oberwolfach
