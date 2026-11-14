module

public import Oberwolfach.AmbientHubCycleProfiles
public import Oberwolfach.SupportedResourceFactors

@[expose] public section

/-! Exact factors in the actual marked cycle family on two hub-neighbour
classes embedded in an ambient host. Both absorber abundance and root enumeration are proved;
no factor or absorber-existence hypothesis is added. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_hub_factor (m : ℕ) (hm : 3<m+1) (β b₀ B₀ : ℝ)
    (hβ : 0<β) (hb₀ : 0<b₀) (hB₀ : 0≤B₀) :
    ∃ η : ℝ,0<η ∧ ∃ k₀ : ℕ,∀ k : ℕ,k₀≤k →
      ∀ (V : Bool → Type) [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
        (A U E K : Type) [Fintype A] [DecidableEq A],
      (∀ i,Fintype.card (V i)=twoClassProfile m i*k) →
      ∀ (e : (Σ i,V i) ↪ A) (tail head : E → A) (ktail khead : K → A)
        (π : Equiv.Perm A) (b : ℕ) (H₀ Hₖ : A → U → Prop) (w : U),
      (∀ v,Hₖ v w ↔ ∃ z : V true,e ⟨true,z⟩=v) →
      (∀ v,H₀ v w ↔ ∃ z : V false,e ⟨false,z⟩=v) →
      β*(Fintype.card A:ℝ)^(m+1)≤
        Fintype.card (HubMarkedCycle tail head ktail khead m π b H₀ Hₖ w) →
      (∀ j : Bool,∀ v v' : A,v≠v' →
        (if j then Hₖ v w else H₀ v w) → (if j then Hₖ v' w else H₀ v' w) →
        β*(Fintype.card A:ℝ)^m≤
          Fintype.card (RootFirstCommonMarkedPath tail head ktail khead m π b H₀ Hₖ j v v' w w)) →
      ∀ wt : HubMarkedCycle tail head ktail khead m π b H₀ Hₖ w → ℝ,
      (∀ C,b₀/(k:ℝ)^m≤wt C ∧ wt C≤B₀/(k:ℝ)^m) →
      (∀ v,|1-hypergraphWeightedDegree (hubMarkedCycleVertices w) wt (e v)|≤η) →
      HasResourceDecomposition (hubMarkedCycleVertices (tail:=tail) (head:=head)
        (ktail:=ktail) (khead:=khead) (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=Hₖ) w) (Finset.univ.image e) := by
  let α := (β/2)^(m+2)*(m+1:ℝ)^((m+1)*(m+1))
  have hα : 0<α := by dsimp [α];positivity
  let S : Unit → VertexAbsorberTemplate (m+1) := fun _ => pairedAbsorberTemplate (m+1)
  have ha (i : Bool) : 1≤twoClassProfile m i := by cases i <;> simp [twoClassProfile] <;> omega
  obtain ⟨η,hη,kf,hfactor⟩  := supported_profile_factor_extraction (twoClassProfile m) (m+1) ((m+1)^(m+1))
    (by omega) ha (twoClassProfile_sum m) S α b₀ B₀ hα hb₀ hB₀
  obtain ⟨N,hN⟩ := paired_absorber_order_threshold m β hβ
  refine ⟨η,hη,max kf N,?_⟩
  intro k hk V _ _ A U E K _ _ hn e tail head ktail khead π b H₀ Hₖ w hK hO hbase hpath wt hw herr
  have htotal : Fintype.card (Σ i,V i)=(m+1)*k := by
    rw [Fintype.card_sigma]
    simp_rw [hn]
    rw [← Finset.sum_mul,twoClassProfile_sum]
  have hcard : (m+1)*k≤Fintype.card A := by
    rw [← htotal]
    exact Fintype.card_le_of_injective e e.injective
  have hNn : N≤Fintype.card A := by
    have hNk := (le_max_right kf N).trans hk
    exact (hNk.trans (by nlinarith : k≤(m+1)*k)).trans hcard
  let C := HubMarkedCycle tail head ktail khead m π b H₀ Hₖ w
  let R : C → Finset A := hubMarkedCycleVertices w
  apply hfactor k ((le_max_left kf N).trans hk) V A C hn e R wt
    (hubMarkedCycle_supported e w hK hO) (ambient_hubMarkedCycle_profile e w hK hO)
    (ambient_hubMarkedCycle_multiplicity w)
    (by simpa only [Nat.add_sub_cancel] using hw) herr
  intro σ
  obtain ⟨x,hx,hxset,hxK,hxO⟩ := exists_twoClass_root_order σ
  have hxhub : MarkedHubCompatible H₀ Hₖ (fun j => e (x j)) w := by
    constructor
    · exact (hK _).mpr ((embedded_class_image_iff e true (x 0)).mpr hxK)
    · intro j
      exact (hO _).mpr ((embedded_class_image_iff e false (x j.succ)).mpr (hxO j))
  have hcount := marked_hub_paired_absorber_count hm w (fun j => e (x j)) (e.injective.comp hx)
    hxhub β hβ hbase hpath (hN _ hNn).1 (hN _ hNn).2
  have hscale : α*(k:ℝ)^((m+1)*(m+1))≤
      (β/2)^(m+2)*(Fintype.card A:ℝ)^((m+1)*(m+1)) := by
    have hcardR : (m+1:ℝ)*k≤Fintype.card A := by exact_mod_cast hcard
    calc
      _ = (β/2)^(m+2)*((m+1:ℝ)*k)^((m+1)*(m+1)) := by dsimp [α];rw [mul_pow];ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hcardR _) (by positivity)
  have hroot : Finset.univ.image (fun j => e (x j))=(profileRootSet σ).image e := by
    rw [← hxset,Finset.image_image]
    rfl
  rw [hroot] at hcount
  let embed : LabelledCycleRecord R (pairedAbsorberTemplate (m+1)).val ((profileRootSet σ).image e) →
      LabelledAbsorberFamily R S ((profileRootSet σ).image e) := fun D => ⟨(),D⟩
  have he : Function.Injective embed := by
    intro D E he
    exact eq_of_heq (Sigma.mk.inj_iff.mp he).2
  exact (hscale.trans hcount).trans (by exact_mod_cast Fintype.card_le_of_injective embed he)

end Oberwolfach
