module

public import Oberwolfach.HubCommonPathCycles

@[expose] public section

/-! Paired absorbers for the actual marked cycle family at one hub.
Common-path hypotheses are needed only for distinct roots of the same type. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K : Type*} [Fintype V] [DecidableEq V]
  {tail head : E → V} {ktail khead : K → V} {m : ℕ}
  {π : Equiv.Perm V} {b : ℕ} {H₀ Hₖ : V → U → Prop}

theorem marked_hub_paired_absorber_count (hm : 3<m+1) (w : U)
    (x : Fin (m+1) → V) (hx : Function.Injective x)
    (hxhub : MarkedHubCompatible H₀ Hₖ x w)
    (β : ℝ) (hβ : 0<β)
    (hbase : β*(Fintype.card V:ℝ)^(m+1)≤
      Fintype.card (HubMarkedCycle tail head ktail khead m π b H₀ Hₖ w))
    (hpath : ∀ j : Bool,∀ v v' : V,v≠v' →
      (if j then Hₖ v w else H₀ v w) → (if j then Hₖ v' w else H₀ v' w) →
      β*(Fintype.card V:ℝ)^m≤
        Fintype.card (RootFirstCommonMarkedPath tail head ktail khead m π b H₀ Hₖ j v v' w w))
    (hnbase : 2*(m+1:ℝ)^2≤β*Fintype.card V)
    (hnpath : 2*(m:ℝ)*(2*(m+1)+(m+1)*m)≤β*Fintype.card V) :
    (β/2)^(m+2)*(Fintype.card V:ℝ)^((m+1)*(m+1))≤
      Fintype.card (LabelledCycleRecord
        (hubMarkedCycleVertices (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
          (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=Hₖ) w)
        (pairedAbsorberTemplate (m+1)).val (Finset.univ.image x)) := by
  let Base := fun y : Fin (m+1) → V =>
    IsMarkedCycleTuple tail head ktail khead m π b y ∧ MarkedHubCompatible H₀ Hₖ y w
  let Path := fun (y : Fin (m+1) → V) (n : ℕ) (g : Fin m → V) =>
    ∃ i : Fin (m+1),i.val=n ∧ ∃ p : RootFirstCommonMarkedPath tail head ktail khead m π b
      H₀ Hₖ (markedPositionType i) (x i) (y i) w w,p.val=g
  have htype (f : Fin (m+1) → V) (hf : MarkedHubCompatible H₀ Hₖ f w) (i : Fin (m+1)) :
      if markedPositionType i then Hₖ (f i) w else H₀ (f i) w :=
    (markedHubCompatible_iff_positions H₀ Hₖ f w).mp hf i
  apply paired_absorber_abundance _ (by omega) x hx Base Path β hβ
    (fun y hy => permutationSeparated_injective π b y hy.1.1)
    (fun y hy => ⟨⟨y,hy⟩,rfl⟩) ?_ ?_ (by convert hbase using 1 <;> congr!) ?_ hnbase hnpath
  · intro y hy hay i g hp
    rcases hp with ⟨i',hi,p,rfl⟩
    have he : i'=i := Fin.ext hi
    subst i'
    have hh := rootFirstCommonMarkedPath_hub_cycles hm w (markedPositionType i) (x i) (y i)
      (htype x hxhub i) (htype y hy.2 i) p
    exact ⟨hh.2,hh.1⟩
  · intro y hy hay n hn g hp
    rcases hp with ⟨i,hi,p,rfl⟩
    exact (rootFirstCommonMarkedPath_labels (markedPositionType i) (x i) (y i) w w p).1
  · intro y hy hay n hn
    let i : Fin (m+1) := ⟨n,hn⟩
    have hne : x i≠y i := by
      intro he
      exact hay i (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he⟩)
    have hh := hpath (markedPositionType i) (x i) (y i) hne (htype x hxhub i) (htype y hy.2 i)
    let embed : RootFirstCommonMarkedPath tail head ktail khead m π b H₀ Hₖ
        (markedPositionType i) (x i) (y i) w w → {g // Path y n g} :=
      fun p => ⟨p.val,i,rfl,p,rfl⟩
    have hi : Function.Injective embed := by
      intro p q he
      apply Subtype.ext
      exact congrArg (fun z : {g // Path y n g} => z.val) he
    have hcard : (Fintype.card (RootFirstCommonMarkedPath tail head ktail khead m π b H₀ Hₖ
        (markedPositionType i) (x i) (y i) w w):ℝ)≤Fintype.card {g // Path y n g} := by
      exact_mod_cast Fintype.card_le_of_injective embed hi
    apply hh.trans
    convert hcard using 1 <;> congr!

end Oberwolfach
