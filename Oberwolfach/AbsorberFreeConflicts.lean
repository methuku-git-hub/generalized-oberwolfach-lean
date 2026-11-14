module

public import Oberwolfach.AbsorberFreeIncidence

@[expose] public section

/-! Intersecting pairs of free configurations are bounded by charging
an actual shared vertex. Diagonal pairs may be counted in this upper
bound; the selection experiment later excludes them. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 2600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C T : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
    [Fintype T] [DecidableEq T] {c : ℕ}

theorem free_absorber_intersection_count (R : C → Finset V) (S : T → VertexAbsorberTemplate c)
    (J : ℕ) (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J)
    (F : FreeAbsorberFamily R S) :
    Fintype.card {G : FreeAbsorberFamily R S // ¬Disjoint (freeFamilyVertices R S F) (freeFamilyVertices R S G)} ≤
      (c*c)^2*Fintype.card T*Fintype.card V^(c*c-1)*J^c := by
  let A := freeFamilyVertices R S F
  have he (G : FreeAbsorberFamily R S) : ¬Disjoint A (freeFamilyVertices R S G) ↔
      ∃ v : A,v.val∈freeFamilyVertices R S G := by
    constructor
    · intro hd
      by_contra hn
      exact hd (Finset.disjoint_left.mpr (fun v hv hw => hn ⟨⟨v,hv⟩,hw⟩))
    · rintro ⟨v,hv⟩ hd;exact Finset.disjoint_left.mp hd v.property hv
  have hcard : Fintype.card {G : FreeAbsorberFamily R S // ¬Disjoint A (freeFamilyVertices R S G)}=
      Fintype.card {G : FreeAbsorberFamily R S // ∃ v : A,v.val∈freeFamilyVertices R S G} :=
    Fintype.card_congr (Equiv.subtypeEquivRight he)
  change Fintype.card {G : FreeAbsorberFamily R S // ¬Disjoint A (freeFamilyVertices R S G)} ≤ _
  rw [hcard]
  calc
    _ ≤ ∑ v : A,Fintype.card {G : FreeAbsorberFamily R S // v.val∈freeFamilyVertices R S G} := by
      convert finite_exists_card_le_sum (fun (v : A) G => v.val∈freeFamilyVertices R S G) using 1 <;> congr!
    _ ≤ ∑ _v : A,(c*c)*Fintype.card T*Fintype.card V^(c*c-1)*J^c :=
      Finset.sum_le_sum (fun v _ => free_absorber_family_vertex_count R S J hJ v.val)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,smul_eq_mul]
      rw [show A.card=c*c from free_absorber_vertex_count R (S F.1) F.2]
      ring

theorem free_absorber_intersecting_pairs_count (hc : 1 ≤ c) (R : C → Finset V)
    (S : T → VertexAbsorberTemplate c) (J : ℕ)
    (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J) :
    Fintype.card {p : FreeAbsorberFamily R S × FreeAbsorberFamily R S //
      ¬Disjoint (freeFamilyVertices R S p.1) (freeFamilyVertices R S p.2)} ≤
      (Fintype.card T)^2*(c*c)^2*J^(2*c)*Fintype.card V^(2*(c*c)-1) := by
  let A := FreeAbsorberFamily R S
  let P := fun F G : A => ¬Disjoint (freeFamilyVertices R S F) (freeFamilyVertices R S G)
  let e : {p : A×A // P p.1 p.2} ≃ Σ F : A,{G : A // P F G} := {
    toFun p := ⟨p.val.1,⟨p.val.2,p.property⟩⟩
    invFun p := ⟨(p.1,p.2.val),p.2.property⟩
    left_inv := by rintro ⟨⟨F,G⟩,h⟩;rfl
    right_inv := by rintro ⟨F,⟨G,h⟩⟩;rfl }
  have he : Fintype.card {p : A×A // P p.1 p.2}=∑ F : A,Fintype.card {G : A // P F G} := by
    simpa only [Fintype.card_sigma] using Fintype.card_congr e
  change Fintype.card {p : A×A // P p.1 p.2} ≤ _
  rw [he]
  calc
    _ ≤ ∑ _F : A,(c*c)^2*Fintype.card T*Fintype.card V^(c*c-1)*J^c :=
      Finset.sum_le_sum (fun F _ => free_absorber_intersection_count R S J hJ F)
    _ = Fintype.card A*((c*c)^2*Fintype.card T*Fintype.card V^(c*c-1)*J^c) := by simp
    _ ≤ (Fintype.card T*Fintype.card V^(c*c)*J^c)*
        ((c*c)^2*Fintype.card T*Fintype.card V^(c*c-1)*J^c) :=
      Nat.mul_le_mul_right _ (free_absorber_family_card R S J hJ)
    _ = _ := by
      have hh : 1 ≤ c*c := by nlinarith
      have hn : Fintype.card V^(2*(c*c)-1)=Fintype.card V^(c*c)*Fintype.card V^(c*c-1) := by
        rw [← pow_add]
        congr 1;omega
      have hJ' : J^(2*c)=J^c*J^c := by rw [show 2*c=c+c by omega,pow_add]
      rw [hn,hJ'];ring

end Oberwolfach
