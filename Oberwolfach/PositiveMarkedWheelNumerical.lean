module

public import Oberwolfach.PositiveMarkedWheelWeights
public import Oberwolfach.ConstantSpokeIntersections
public import Oberwolfach.RootFirstCommonPaths

@[expose] public section

/-! The marked-wheel criterion with the manuscript's constant spoke
profiles and root-first common-path families. No correction operators or
unproved existence statements are assumed by this public result. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
universe u v w z
attribute [local instance] Classical.propDecidable

theorem positive_marked_wheel_weights_numerical_uniform (α p₀ : ℝ)
    (hα : 0<α) (hαmax : α≤1) (hp₀ : 0<p₀) (hp₀max : p₀≤1/2) :
    ∃ c₀ : ℕ,∀ k : ℕ,c₀≤k+2 → ∀ pstar β bminus bplus : ℝ,
    0<β → 0<pstar → 0<bminus → 0<bplus →
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
    ∀ (varsigma : Bool → ℝ) (δsp Dexc : ℝ),
    (∀ j,pstar≤varsigma j ∧ varsigma j≤1) → 0≤δsp → 0≤Dexc →
    (∀ j,∀ S : Finset U,1≤S.card → S.card≤3 →
      |((commonSpokeNeighbours (if j then Hₖ else H₀) S).card:ℝ)-
        (varsigma j)^S.card*Fintype.card V|≤δsp*Fintype.card V) →
    (∀ j x,∃ E' : Finset V,(E'.card:ℝ)≤Dexc ∧ ∀ y,y∉E' →
      |((Finset.univ.filter (fun u=>(if j then Hₖ x u else H₀ x u) ∧
        (if j then Hₖ y u else H₀ y u))).card:ℝ)-(varsigma j)^2*Fintype.card U|≤
        δsp*(varsigma j)^2*Fintype.card U) →
    δsp+Dexc/(Fintype.card V:ℝ)+1/(Fintype.card U:ℝ)≤δ₀ →
    (∀ u u' : U,u≠u' → β*(Fintype.card V:ℝ)^(k+2)≤
      (Fintype.card (CommonMarkedCycle tail head ktail khead (k+1) π b H₀ Hₖ u u'):ℝ)) →
    (∀ j,∀ v v' : V,∀ u u' : U,v≠v' → u≠u' →
      (if j then Hₖ v u else H₀ v u) → (if j then Hₖ v u' else H₀ v u') →
      (if j then Hₖ v' u else H₀ v' u) → (if j then Hₖ v' u' else H₀ v' u') →
      β*(Fintype.card V:ℝ)^(k+1)≤
        (Fintype.card (RootFirstCommonMarkedPath tail head ktail khead (k+1) π b H₀ Hₖ j v v' u u'):ℝ)) →
    ∀ η : ℝ,0≤η → η≤η₀ →
    ∀ ψ : MarkedWheel tail head ktail khead (k+1) π b H₀ Hₖ → ℝ,
    (∀ e,|markedWheelRimLoad ψ e-1|≤η) →
    (∀ j v u,|markedSpokeResidual ψ j v u|≤η) →
    (∀ W,bminus/(Fintype.card V:ℝ)^(k+1)≤ψ W ∧ ψ W≤bplus/(Fintype.card V:ℝ)^(k+1)) →
    ∃ w : MarkedWheel tail head ktail khead (k+1) π b H₀ Hₖ → ℝ,
      (∀ e,markedWheelRimLoad w e=1) ∧
      (∀ j v u,markedWheelSpokeLoad w j v u=if (if j then Hₖ v u else H₀ v u) then 1 else 0) ∧
      (∀ W,(bminus/2)/(Fintype.card V:ℝ)^(k+1)≤w W ∧ w W≤A/(Fintype.card V:ℝ)^(k+1)) := by
  obtain ⟨c₀,hc₀⟩ := positive_marked_wheel_weights_uniform_parameters.{u,v,w,z}
    α p₀ hα hαmax hp₀ hp₀max
  refine ⟨max c₀ 8,?_⟩
  intro k hk pstar β bminus bplus hβ hpstar hbm hbp
  let L := max 1 (1/pstar)
  have hkm : 3<(k+1)+1 := by omega
  obtain ⟨ε,η₀,δ₀,A,hε,hη₀,hδ₀,hA,hh⟩ := hc₀ k ((le_max_left _ _).trans hk) β L bminus bplus hβ (le_max_left _ _) hbm hbp
  refine ⟨ε,η₀,δ₀,A,hε,hη₀,hδ₀,hA,?_⟩
  intro b
  obtain ⟨n₀,hn₀⟩ := hh b
  refine ⟨n₀,?_⟩
  intro V E K U _ _ _ _ _ _ tail head ktail khead π hphys p D hp hpmax hn hDlo hDhi hdo hdi hdko hdki htwo hcut
    H₀ Hₖ hhub hdir hK hout hcol hu varsigma δsp Dexc hvar hδ hDexc hinter hcodeg hsmall hcommon hpaths
    η hη hηmax ψ hRerr hSerr hψ
  let i : Bool → Fin (k+2) := fun j=>(markedRootOrder (k+1) j).symm 0
  have hdata (j : Bool) : SparseIntersectionData (if j then Hₖ else H₀)
      (fun _=>varsigma j) (fun _=>1/varsigma j) L δsp Dexc := by
    apply sparseIntersectionData_of_constant_density (if j then Hₖ else H₀)
      (varsigma j) pstar δsp Dexc hpstar (hvar j).1 (hvar j).2 hδ hDexc (hinter j)
    simpa only [ite_apply] using hcodeg j
  have hreplace (j : Bool) (Q : BipartiteFourCycle (if j then Hₖ else H₀)) :
      β*(Fintype.card V:ℝ)^(k+1)≤
        (Fintype.card (MarkedReplacementPair tail head ktail khead (k+1) π b H₀ Hₖ (i j)
          Q.val.1.1 Q.val.1.2 Q.val.2.1 Q.val.2.2):ℝ) := by
    have hr : (if j then Hₖ Q.val.1.1 Q.val.2.1 else H₀ Q.val.1.1 Q.val.2.1) ∧
        (if j then Hₖ Q.val.1.1 Q.val.2.2 else H₀ Q.val.1.1 Q.val.2.2) ∧
        (if j then Hₖ Q.val.1.2 Q.val.2.1 else H₀ Q.val.1.2 Q.val.2.1) ∧
        (if j then Hₖ Q.val.1.2 Q.val.2.2 else H₀ Q.val.1.2 Q.val.2.2) := by
      simpa only [ite_apply] using
        And.intro Q.property.2.2.1 (And.intro Q.property.2.2.2.2.2
          (And.intro Q.property.2.2.2.1 Q.property.2.2.2.2.1))
    exact (hpaths j _ _ _ _ Q.property.1 Q.property.2.1 hr.1 hr.2.1 hr.2.2.1 hr.2.2.2).trans
      (by
        have hc := rootFirstCommonMarkedPath_card_le (tail:=tail) (head:=head)
          (ktail:=ktail) (khead:=khead) (π:=π) (b:=b) hkm j _ _ _ _ hr
        dsimp only [i]
        simp only [← Nat.card_eq_fintype_card] at hc ⊢
        exact_mod_cast hc)
  exact hn₀ V E K U tail head ktail khead π hphys p D hp hpmax hn hDlo hDhi hdo hdi hdko hdki htwo hcut
    H₀ Hₖ hhub hdir hK hout hcol hu (fun j _=>varsigma j) (fun j _=>1/varsigma j) δsp Dexc
    hdata hsmall i (fun j=>markedRootOrder_type (k+1) hkm j) hcommon hreplace η hη hηmax ψ hRerr hSerr hψ

theorem positive_marked_wheel_weights_numerical (α p₀ pstar β bminus bplus : ℝ)
    (hα : 0<α) (hαmax : α≤1) (hp₀ : 0<p₀) (hp₀max : p₀≤1/2) (hβ : 0<β)
    (hpstar : 0<pstar) (hbm : 0<bminus) (hbp : 0<bplus) :
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
    ∀ (varsigma : Bool → ℝ) (δsp Dexc : ℝ),
    (∀ j,pstar≤varsigma j ∧ varsigma j≤1) → 0≤δsp → 0≤Dexc →
    (∀ j,∀ S : Finset U,1≤S.card → S.card≤3 →
      |((commonSpokeNeighbours (if j then Hₖ else H₀) S).card:ℝ)-
        (varsigma j)^S.card*Fintype.card V|≤δsp*Fintype.card V) →
    (∀ j x,∃ E' : Finset V,(E'.card:ℝ)≤Dexc ∧ ∀ y,y∉E' →
      |((Finset.univ.filter (fun u=>(if j then Hₖ x u else H₀ x u) ∧
        (if j then Hₖ y u else H₀ y u))).card:ℝ)-(varsigma j)^2*Fintype.card U|≤
        δsp*(varsigma j)^2*Fintype.card U) →
    δsp+Dexc/(Fintype.card V:ℝ)+1/(Fintype.card U:ℝ)≤δ₀ →
    (∀ u u' : U,u≠u' → β*(Fintype.card V:ℝ)^(k+2)≤
      (Fintype.card (CommonMarkedCycle tail head ktail khead (k+1) π b H₀ Hₖ u u'):ℝ)) →
    (∀ j,∀ v v' : V,∀ u u' : U,v≠v' → u≠u' →
      (if j then Hₖ v u else H₀ v u) → (if j then Hₖ v u' else H₀ v u') →
      (if j then Hₖ v' u else H₀ v' u) → (if j then Hₖ v' u' else H₀ v' u') →
      β*(Fintype.card V:ℝ)^(k+1)≤
        (Fintype.card (RootFirstCommonMarkedPath tail head ktail khead (k+1) π b H₀ Hₖ j v v' u u'):ℝ)) →
    ∀ η : ℝ,0≤η → η≤η₀ →
    ∀ ψ : MarkedWheel tail head ktail khead (k+1) π b H₀ Hₖ → ℝ,
    (∀ e,|markedWheelRimLoad ψ e-1|≤η) →
    (∀ j v u,|markedSpokeResidual ψ j v u|≤η) →
    (∀ W,bminus/(Fintype.card V:ℝ)^(k+1)≤ψ W ∧ ψ W≤bplus/(Fintype.card V:ℝ)^(k+1)) →
    ∃ w : MarkedWheel tail head ktail khead (k+1) π b H₀ Hₖ → ℝ,
      (∀ e,markedWheelRimLoad w e=1) ∧
      (∀ j v u,markedWheelSpokeLoad w j v u=if (if j then Hₖ v u else H₀ v u) then 1 else 0) ∧
      (∀ W,(bminus/2)/(Fintype.card V:ℝ)^(k+1)≤w W ∧ w W≤A/(Fintype.card V:ℝ)^(k+1)) := by
  obtain ⟨c₀,hc₀⟩ := positive_marked_wheel_weights_numerical_uniform.{u,v,w,z} α p₀ hα hαmax hp₀ hp₀max
  exact ⟨c₀,fun k hk=>hc₀ k hk pstar β bminus bplus hβ hpstar hbm hbp⟩

end Oberwolfach
