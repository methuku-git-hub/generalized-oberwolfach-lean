module

public import Oberwolfach.LongDualResidualTypedHost
public import Oberwolfach.LongEligibleMarkedIncomingChange
public import Oberwolfach.MarkedHostRawEncoding

@[expose] public section
/-! Encode the entire corrected residual on the same raw sample, keeping all
interval coordinates and the original protected-inner rim coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
local instance dualRawEncodingDecEq : DecidableEq V := Classical.decEq V
local instance dualRawEncodingArc (P:V×V→Prop):DecidableEq {e:V×V // P e}:=Classical.decEq _

theorem long_dual_residual_raw_encoding
    (G S Small:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (Mhost:V→V→ℕ)
    (hphysical:∀x y,Mhost x y+Mhost y x=if S.Adj x y then 1 else 0)
    (hhost:∀x y,Mhost x y=1→G.Adj x y)
    (raw:RawMarkedOutcome V U Γ Color) (I:Finset V) (hI:∀v,π v∈I↔v∈I):
    let P:=longEligibleResidualArc Mhost Small ⊥;
    ∀T:Finset {e:V×V // P e},(∀e∈T,longMarkedArcEligible π d e.val)→(∀e,e∉T→longOrdinaryArcEligible π d e.val)→
    let E:=residualOrdinaryArc P T
    let K:=residualMarkedArc P T
    let tail:=fun e:E=>e.val.val.1
    let head:=fun e:E=>e.val.val.2
    let ktail:=fun e:K=>e.val.val.1
    let khead:=fun e:K=>π.symm e.val.val.2;
    (∀mark x y,x∈I→y∈I→
      (markedPhysicalRim G π (3*d) (fun e=>raw (Sum.inl e)) mark x y=1 ↔
        if mark then ∃e:K,ktail e=x∧khead e=y else ∃e:E,tail e=x∧head e=y))→
    let τ:=rawMarkedEncodeHost tail head ktail khead π raw I;
    (∀e,τ (Sum.inr e)=raw (Sum.inr e)) ∧
    (∀e:Sym2 V,e.toFinset⊆I→τ (Sum.inl e)=raw (Sum.inl e)) ∧
    (∀mark x y,markedPhysicalRim G π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1 ↔
      if mark then ∃e:K,ktail e=x∧khead e=y else ∃e:E,tail e=x∧head e=y):=by
  intro P T hMarked hOrd E K tail head ktail khead hInner τ
  have hprops:=long_dual_residual_typed_host_properties G S Small π d Mhost hphysical hhost T hMarked hOrd
  refine ⟨(fun _=>rfl),?_,?_⟩
  · intro e he
    exact rawMarkedEncodeHost_inner_coordinates tail head ktail khead π raw I e he
  · intro mark x y
    exact rawMarkedEncodeHost_rims G π d tail head ktail khead hprops.1 hprops.2.1 hprops.2.2 raw I hI hInner mark x y
end Oberwolfach
