module

public import Oberwolfach.AbsorberFreeCounts
public import Oberwolfach.AbsorberFreeFactors
public import Oberwolfach.AbsorberFamilyCounts

@[expose] public section

/-! The root-free configuration family, its size, and the bounded
multiplicity of the map forgetting roots and the second factor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option synthInstance.maxSize 256
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C T : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
    [Fintype T] [DecidableEq T] {c : ℕ}

abbrev FreeAbsorberFamily (R : C → Finset V) (S : T → VertexAbsorberTemplate c) :=
  Σ t,FreeAbsorberRecord R (S t)

def familyForgetAbsorberRoots (R : C → Finset V) (S : T → VertexAbsorberTemplate c)
    (X : Finset V) (D : LabelledAbsorberFamily R S X) : FreeAbsorberFamily R S :=
  ⟨D.1,forgetAbsorberRoots R (S D.1) X D.2⟩

theorem labelledAbsorberFamily_ext (R : C → Finset V) (S : T → VertexAbsorberTemplate c)
    (X : Finset V) (D E : LabelledAbsorberFamily R S X) (ht : D.1=E.1)
    (hf : ∀ j,D.2.1.val j=E.2.1.val j) (hg : ∀ o,(D.2.2 o).val=(E.2.2 o).val) : D=E := by
  rcases D with ⟨t,D⟩
  rcases E with ⟨u,E⟩
  change t=u at ht
  subst u
  exact congrArg (Sigma.mk t) (labelledCycleRecord_ext R (S t).val X D E hf hg)

theorem free_absorber_family_card (R : C → Finset V) (S : T → VertexAbsorberTemplate c) (J : ℕ)
    (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J) :
    Fintype.card (FreeAbsorberFamily R S) ≤ Fintype.card T*Fintype.card V^(c*c)*J^c := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _t : T,Fintype.card V^(c*c)*J^c :=
      Finset.sum_le_sum (fun t _ => free_absorber_records_card R (S t) J hJ)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul];ring

theorem family_forget_absorber_roots_fibre_card (R : C → Finset V) (S : T → VertexAbsorberTemplate c)
    (X : Finset V) (J : ℕ)
    (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J) (F : FreeAbsorberFamily R S) :
    Fintype.card {D : LabelledAbsorberFamily R S X // familyForgetAbsorberRoots R S X D=F} ≤
      Fintype.card T*X.card^c*J^(c+1) := by
  obtain ⟨code,hcode⟩ := finite_fibre_codes R J hJ
  let A := {D : LabelledAbsorberFamily R S X // familyForgetAbsorberRoots R S X D=F}
  let enc (D : A) : T × (Fin c → X) × (Fin (c+1) → Fin J) :=
    (D.val.1,fun i => ⟨D.val.2.1.val (Sum.inr i),rootedLabelMap_root_mem X D.val.2.1 i⟩,
     fun i => code (D.val.2.2 (Sum.inr i)).val)
  have hinj : Function.Injective enc := by
    intro D E he
    have ht : D.val.1=E.val.1 := congrArg Prod.fst he
    have hf (j : Fin (c*c) ⊕ Fin c) : D.val.2.1.val j=E.val.2.1.val j := by
      rcases j with j | j
      · have hd := congrArg (fun F : FreeAbsorberFamily R S => F.2.1 j) D.property
        have he' := congrArg (fun F : FreeAbsorberFamily R S => F.2.1 j) E.property
        exact hd.trans he'.symm
      · exact congrArg (fun z : X => z.val) (congrFun (congrArg (fun z => z.2.1) he) j)
    apply Subtype.ext
    apply labelledAbsorberFamily_ext R S X D.val E.val ht hf
    intro o
    rcases o with i | i
    · have hd := congrArg (fun F : FreeAbsorberFamily R S => (F.2.2 i).val) D.property
      have he' := congrArg (fun F : FreeAbsorberFamily R S => (F.2.2 i).val) E.property
      exact hd.trans he'.symm
    · apply hcode
      · rw [(D.val.2.2 (Sum.inr i)).property,(E.val.2.2 (Sum.inr i)).property]
        have hs := congrArg (fun t => (S t).val (Sum.inr i)) ht
        exact (congrArg (Finset.image D.val.2.1.val) hs).trans
          (congrArg (Finset.image · ((S E.val.1).val (Sum.inr i))) (funext hf))
      · exact congrFun (congrArg (fun z => z.2.2) he) i
  have hh := Fintype.card_le_of_injective enc hinj
  simpa only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,mul_assoc] using hh

end Oberwolfach
