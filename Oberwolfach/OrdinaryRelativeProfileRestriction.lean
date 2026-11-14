module

public import Oberwolfach.OrdinaryRestrictedProfileLoads
public import Oberwolfach.OrdinaryRestrictedProfileAbsorbers
public import Oberwolfach.OrdinaryProfileRescaling
public import Oberwolfach.OrdinaryProfileDeletionMargins

@[expose] public section

/-! The common-cycle profiles used by an ordinary transformer after linear
row deletions and bounded rim deletions. The tolerance is fixed before the
forbidden-edge allowance; the coefficients on surviving cycles are unchanged. -/
set_option autoImplicit false
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Tpl : Type} [Fintype Tpl] [DecidableEq Tpl]

theorem ordinary_relative_profile_restriction (r : ℕ) (hr : 3≤r)
    (S : Tpl → VertexAbsorberTemplate r) (β a b B τ : ℝ)
    (hβ : 0<β) (ha : 0<a) (hb : 0<b) (hB : 0<B) (hτ : 0<τ) :
    ∃ ε : ℝ,0<ε ∧ ε≤β/2 ∧ ∀ f : ℕ,∃ N : ℕ,1≤N ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V],N≤Fintype.card V →
      ∀ (Q D F : SimpleGraph V) (T Z : Finset V),
      β*Fintype.card V≤(T.card:ℝ) → (Z.card:ℝ)≤ε*Fintype.card V → D.edgeFinset.card≤f →
      ∀ w : LocalOrdinaryCycle Q F T r → ℝ,
      (∀ C,b/(Fintype.card V:ℝ)^(r-1)≤w C ∧ w C≤B/(Fintype.card V:ℝ)^(r-1)) →
      (∀ v∈T,|1-hypergraphWeightedDegree localOrdinaryVertices w v|≤τ/4) →
      (∀ X : Finset V,X⊆T → X.card=r →
        a*(Fintype.card V:ℝ)^(r*r)≤Fintype.card (LabelledAbsorberFamily (localOrdinaryVertices (Q:=Q) (F:=F) (T:=T) (r:=r)) S X)) →
      let k := ((T\Z).card:ℝ)/r
      let w' := fun C : LocalOrdinaryCycle (Q\D) F (T\Z) r=>
        w (localOrdinaryRestrictionParent sdiff_le Finset.sdiff_subset C)
      0<k ∧ (β/2)*Fintype.card V≤(r:ℝ)*k ∧ (r:ℝ)*k≤Fintype.card V ∧
      (∀ C,(b*(β/2)^(r-1)/(r:ℝ)^(r-1))/k^(r-1)≤w' C ∧
        w' C≤(B/(r:ℝ)^(r-1))/k^(r-1)) ∧
      (∀ v∈T\Z,|1-hypergraphWeightedDegree localOrdinaryVertices w' v|≤3*τ/4) ∧
      (∀ X : Finset V,X⊆T\Z → X.card=r →
        ((a/2)*(r:ℝ)^(r*r))*k^(r*r)≤
          Fintype.card (LabelledAbsorberFamily (localOrdinaryVertices (Q:=Q\D) (F:=F) (T:=T\Z) (r:=r)) S X)) := by
  let K : ℝ := (r^r:ℕ)*B
  let L : ℝ := ordinaryAbsorberDeletionCoefficient r (Fintype.card Tpl)
  have hK : 0≤K := by dsimp [K];positivity
  have hL : 0≤L := Nat.cast_nonneg _
  obtain ⟨ε,hε,hεβ,hN⟩ := ordinary_profile_deletion_margins β a τ K L hβ ha hτ hK hL
  refine ⟨ε,hε,hεβ,?_⟩
  intro f
  obtain ⟨N,hN1,hN⟩ := hN f
  refine ⟨N,hN1,?_⟩
  intro V _ _ hn Q D F T Z hT hZ hD w hw herr habs
  dsimp only
  let k : ℝ := ((T\Z).card:ℝ)/r
  have hn1 : 1≤Fintype.card V := hN1.trans hn
  have hnR : (0:ℝ)<Fintype.card V := by exact_mod_cast (show 0<Fintype.card V by omega)
  have hrR : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have hcard : T.card≤(T\Z).card+Z.card := by
    apply (Finset.card_le_card (show T⊆(T\Z)∪Z from ?_)).trans (Finset.card_union_le _ _)
    intro v hv
    by_cases hz : v∈Z
    · exact Finset.mem_union_right _ hz
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hv,hz⟩)
  have hcardR : (T.card:ℝ)≤((T\Z).card:ℝ)+Z.card := by exact_mod_cast hcard
  have hscale : (r:ℝ)*k=(T\Z).card := by dsimp [k];field_simp
  have hlow : (β/2)*Fintype.card V≤(r:ℝ)*k := by
    rw [hscale]
    have hh := mul_le_mul_of_nonneg_right hεβ hnR.le
    linarith only [hT,hZ,hcardR,hh]
  have hhigh : (r:ℝ)*k≤Fintype.card V := by
    rw [hscale]
    exact_mod_cast Finset.card_le_univ (T\Z)
  have hk : 0<k := by nlinarith only [hlow,mul_pos (half_pos hβ) hnR,hrR]
  obtain ⟨hload,habsloss⟩ := hN (Fintype.card V) hn Z.card D.edgeFinset.card hZ hD
  refine ⟨hk,hlow,hhigh,?_,?_,?_⟩
  · intro C
    exact ordinary_profile_weight_rescale r (by omega) _ k β b B _ hnR hk hβ hb.le hB.le
      (by nlinarith only [hlow]) hhigh (hw _)
  · intro v hv
    have h0 (C : LocalOrdinaryCycle Q F T r) : 0≤w C :=
      (by positivity : (0:ℝ)≤b/(Fintype.card V:ℝ)^(r-1)).trans (hw C).1
    have hh := ordinary_restricted_profile_loads Q D F T Z (by omega) (by omega) w B (τ/4)
      hB.le (fun C=>⟨h0 C,(hw C).2⟩) herr v hv
    have hload' : ((Z.card+D.edgeFinset.card:ℕ):ℝ)*((r^r:ℕ)*B/Fintype.card V)≤τ/2 := by
      convert hload using 1 <;> dsimp [K] <;> ring
    exact hh.trans (by linarith only [hload'])
  · intro X hX hXr
    have hXZ : Disjoint X Z := Finset.disjoint_left.mpr (fun v hv hz=>(Finset.mem_sdiff.mp (hX hv)).2 hz)
    have hh := ordinary_restricted_profile_absorbers Q D F T Z X (by omega) hn1 hXr hXZ S
    have hhR : (Fintype.card (LabelledAbsorberFamily (localOrdinaryVertices (Q:=Q) (F:=F) (T:=T) (r:=r)) S X):ℝ)≤
        Fintype.card (LabelledAbsorberFamily (localOrdinaryVertices (Q:=Q\D) (F:=F) (T:=T\Z) (r:=r)) S X)+
        ((Z.card+D.edgeFinset.card:ℕ):ℝ)*L*(Fintype.card V:ℝ)^(r*r-1) := by
      dsimp only [L]
      exact_mod_cast hh
    have hp : (Fintype.card V:ℝ)*(Fintype.card V:ℝ)^(r*r-1)=(Fintype.card V:ℝ)^(r*r) := by
      rw [←pow_succ']
      congr 1
      have hh : 1≤r*r := by nlinarith
      omega
    have hloss := mul_le_mul_of_nonneg_right habsloss (pow_nonneg hnR.le (r*r-1))
    rw [mul_assoc (a/2),hp] at hloss
    have hparent := habs X (hX.trans Finset.sdiff_subset) hXr
    have hcount : (a/2)*(Fintype.card V:ℝ)^(r*r)≤
        Fintype.card (LabelledAbsorberFamily (localOrdinaryVertices (Q:=Q\D) (F:=F) (T:=T\Z) (r:=r)) S X) := by
      linarith only [hhR,hloss,hparent]
    exact ordinary_profile_absorber_rescale r a _ k _ ha.le hk.le hhigh hcount

end Oberwolfach
