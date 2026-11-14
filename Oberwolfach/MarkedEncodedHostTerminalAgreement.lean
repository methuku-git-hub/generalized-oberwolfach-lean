module

public import Oberwolfach.MarkedHostRawEncoding
public import Oberwolfach.MarkedFiniteRemainderTransfer

@[expose] public section

/-! A terminal arc of an encoded host on the protected inner domain has
an arc of the same type and endpoints in the original sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_encoded_host_terminal_arc_agreement
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (tail head:E→V) (ktail khead:K→V)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hE:∀ e,¬PermutationClose π (3*d) (tail e) (head e)∧P.Adj (tail e) (head e))
    (hK:∀ e,¬PermutationClose π (3*d) (ktail e) (khead e)∧P.Adj (ktail e) (π (khead e)))
    (σ:RawMarkedOutcome V U Γ Color) (I X:Finset V) (hX:X⊆I) (hI:∀ v,π v∈I↔v∈I)
    (hAgree:∀ mark x y,x∈I→y∈I→
      (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ↔
        (if mark then ∃ e:K,ktail e=x∧khead e=y else ∃ e:E,tail e=x∧head e=y))):
    let τ:=rawMarkedEncodeHost tail head ktail khead π σ I
    let Eold:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let Kold:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let Enew:=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) false
    let Knew:=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) true
    let srcOld:=Sum.elim (fun e:Eold=>e.val.1) (fun e:Kold=>e.val.1)
    let dstOld:=Sum.elim (fun e:Eold=>e.val.2) (fun e:Kold=>e.val.2)
    let srcNew:=Sum.elim (fun e:Enew=>e.val.1) (fun e:Knew=>e.val.1)
    let dstNew:=Sum.elim (fun e:Enew=>e.val.2) (fun e:Knew=>e.val.2)
    let A₀:=Finset.univ.filter (fun a:Eold⊕Kold=>srcOld a∈X∧dstOld a∈X);
    ∀ a:Enew⊕Knew,srcNew a∈X→dstNew a∈X→
      ∃ a₀∈A₀,srcOld a₀=srcNew a∧dstOld a₀=dstNew a∧markedArcType a₀=markedArcType a := by
  intro τ Eold Kold Enew Knew srcOld dstOld srcNew dstNew A₀ a hx hy
  cases a with
  | inl e=>
    have hs:= (rawMarkedEncodeHost_rims P π d tail head ktail khead hp hE hK σ I hI hAgree false e.val.1 e.val.2).mp e.property
    have ho:= (hAgree false e.val.1 e.val.2 (hX hx) (hX hy)).mpr hs
    let old:Eold:=⟨e.val,ho⟩
    refine ⟨Sum.inl old,?_,rfl,rfl,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx,hy⟩
  | inr e=>
    have hs:= (rawMarkedEncodeHost_rims P π d tail head ktail khead hp hE hK σ I hI hAgree true e.val.1 e.val.2).mp e.property
    have ho:= (hAgree true e.val.1 e.val.2 (hX hx) (hX hy)).mpr hs
    let old:Kold:=⟨e.val,ho⟩
    refine ⟨Sum.inr old,?_,rfl,rfl,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx,hy⟩

omit [LinearOrder V] in
/-- Agreement of both spoke types on the protected pair supplies the
terminal spoke conditions used in the fixed-reservoir iteration. -/
theorem marked_terminal_spoke_agreement
    (Hold Hnew:Bool→V→U→Prop) (I X:Finset V) (J Y:Finset U)
    (hX:X⊆I) (hY:Y⊆J)
    (hAgree:∀ b v u,v∈I→u∈J→(Hold b v u↔Hnew b v u)):
    let S₀:=Finset.univ.filter (fun z:V×U=>
      (Hold false z.1 z.2∨Hold true z.1 z.2)∧z.1∈X∧z.2∈Y);
    ∀ z:V×U,z.1∈X→z.2∈Y→(Hnew false z.1 z.2∨Hnew true z.1 z.2)→
      z∈S₀ ∧ (Hold false z.1 z.2↔Hnew false z.1 z.2) ∧
        (Hold true z.1 z.2↔Hnew true z.1 z.2) := by
  intro S₀ z hx hy hz
  have h0:=hAgree false z.1 z.2 (hX hx) (hY hy)
  have h1:=hAgree true z.1 z.2 (hX hx) (hY hy)
  refine ⟨?_,h0,h1⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz.elim (fun h=>Or.inl (h0.mpr h)) (fun h=>Or.inr (h1.mpr h)),hx,hy⟩

end Oberwolfach
