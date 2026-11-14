module

public import Oberwolfach.AbsorberFreeFamilies
public import Oberwolfach.FixedFunctionCoordinates
public import Oberwolfach.FiniteExistentialCounts

@[expose] public section

/-! A prescribed free label reduces the configuration count by one
power of the host order. The internal cycle identifiers are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 2800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C T : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
    [Fintype T] [DecidableEq T] {c : ℕ}

theorem freeAbsorberRecord_ext (R : C → Finset V) (S : VertexAbsorberTemplate c)
    (F G : FreeAbsorberRecord R S) (hf : ∀ j,F.1 j=G.1 j)
    (hi : ∀ i,(F.2 i).val=(G.2 i).val) : F=G := by
  rcases F with ⟨f,d⟩
  rcases G with ⟨g,e⟩
  have he : f=g := DFunLike.ext _ _ hf
  subst g
  have he' : d=e := funext (fun i => Subtype.ext (hi i))
  subst e;rfl

theorem free_absorber_coordinate_count (R : C → Finset V) (S : VertexAbsorberTemplate c)
    (J : ℕ) (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J)
    (j : Fin (c*c)) (v : V) :
    Fintype.card {F : FreeAbsorberRecord R S // F.1 j=v} ≤ Fintype.card V^(c*c-1)*J^c := by
  obtain ⟨code,hcode⟩ := finite_fibre_codes R J hJ
  let A := {F : FreeAbsorberRecord R S // F.1 j=v}
  let B := {f : Fin (c*c) → V // f j=v}
  let enc (F : A) : B × (Fin c → Fin J) :=
    (⟨F.val.1,F.property⟩,fun i => code (F.val.2 i).val)
  have hinj : Function.Injective enc := by
    intro F G he
    have hf : ∀ k,F.val.1 k=G.val.1 k := fun k =>
      congrFun (congrArg (fun z : B × (Fin c → Fin J) => z.1.val) he) k
    apply Subtype.ext
    apply freeAbsorberRecord_ext R S F.val G.val hf
    intro i
    apply hcode
    · rw [(F.val.2 i).property,(G.val.2 i).property]
      exact congrArg (Finset.image · (freeLabelPositions (S.val (Sum.inl i)))) (funext hf)
    · exact congrFun (congrArg Prod.snd he) i
  have hh := Fintype.card_le_of_injective enc hinj
  have hb : Fintype.card B=Fintype.card V^(c*c-1) := by
    have hh := finite_function_fixed_value_card j v
    simp only [Fintype.card_fin] at hh
    convert hh using 1 <;> congr!
  simpa only [Fintype.card_prod,hb,Fintype.card_fun,Fintype.card_fin] using hh

def freeFamilyVertices (R : C → Finset V) (S : T → VertexAbsorberTemplate c)
    (F : FreeAbsorberFamily R S) : Finset V := freeAbsorberVertices R (S F.1) F.2

theorem free_absorber_family_vertex_count (R : C → Finset V) (S : T → VertexAbsorberTemplate c)
    (J : ℕ) (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J) (v : V) :
    Fintype.card {F : FreeAbsorberFamily R S // v∈freeFamilyVertices R S F} ≤
      (c*c)*Fintype.card T*Fintype.card V^(c*c-1)*J^c := by
  have hc (j : Fin (c*c)) : Fintype.card {F : FreeAbsorberFamily R S // F.2.1 j=v} ≤
      Fintype.card T*(Fintype.card V^(c*c-1)*J^c) := by
    have he : Fintype.card {F : FreeAbsorberFamily R S // F.2.1 j=v}=
        ∑ t,Fintype.card {F : FreeAbsorberRecord R (S t) // F.1 j=v} := by
      convert finite_sigma_predicate_card (fun t (F : FreeAbsorberRecord R (S t)) => F.1 j=v) using 1 <;> congr!
    rw [he]
    calc
      _ ≤ ∑ _t : T,Fintype.card V^(c*c-1)*J^c :=
        Finset.sum_le_sum (fun t _ => free_absorber_coordinate_count R (S t) J hJ j v)
      _ = _ := by simp
  have he : (fun F : FreeAbsorberFamily R S => v∈freeFamilyVertices R S F)=
      (fun F => ∃ j : Fin (c*c),F.2.1 j=v) := by
    funext F;apply propext;simp [freeFamilyVertices,freeAbsorberVertices]
  have hcard : Fintype.card {F : FreeAbsorberFamily R S // v∈freeFamilyVertices R S F}=
      Fintype.card {F : FreeAbsorberFamily R S // ∃ j : Fin (c*c),F.2.1 j=v} := by
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun F => iff_of_eq (congrFun he F))
  rw [hcard]
  calc
    _ ≤ ∑ j : Fin (c*c),Fintype.card {F : FreeAbsorberFamily R S // F.2.1 j=v} := by
      convert finite_exists_card_le_sum (fun j (F : FreeAbsorberFamily R S) => F.2.1 j=v) using 1 <;> congr!
    _ ≤ ∑ _j : Fin (c*c),Fintype.card T*(Fintype.card V^(c*c-1)*J^c) := Finset.sum_le_sum (fun j _ => hc j)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul];ring

end Oberwolfach
