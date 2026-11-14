module

public import Oberwolfach.MarkedWheelFamilyLoads

@[expose] public section

/-! Hub-use budgets for successive marked wheel choices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K I:Type} [Fintype V] [Fintype U] [Fintype I] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b m:ℕ}

theorem markedFamilyHubLoad_total (C:I→MarkedWheel tail head ktail khead m π b H₀ HK):
    ∑ u,markedFamilyHubLoad C u=Fintype.card I:=by
  simp only [markedFamilyHubLoad,Finset.card_filter]
  rw [Finset.sum_comm]
  simp

theorem markedFamilyHubLoad_saturated (C:I→MarkedWheel tail head ktail khead m π b H₀ HK) (K:ℕ):
    K*(Finset.univ.filter (fun u=>K≤markedFamilyHubLoad C u)).card≤Fintype.card I:=by
  calc
    _=∑ u∈Finset.univ.filter (fun u=>K≤markedFamilyHubLoad C u),K:=by simp [Nat.mul_comm]
    _≤∑ u∈Finset.univ.filter (fun u=>K≤markedFamilyHubLoad C u),markedFamilyHubLoad C u:=
      Finset.sum_le_sum (fun u hu=>(Finset.mem_filter.mp hu).2)
    _≤∑ u,markedFamilyHubLoad C u:=Finset.sum_le_univ_sum_of_nonneg (fun _=>Nat.zero_le _)
    _=_:=markedFamilyHubLoad_total C

theorem markedFamilyHubLoad_snoc {n:ℕ} (C:Fin n→MarkedWheel tail head ktail khead m π b H₀ HK)
    (B:MarkedWheel tail head ktail khead m π b H₀ HK) (u:U):
    markedFamilyHubLoad (Fin.snoc C B) u=markedFamilyHubLoad C u+(if B.2.val=u then 1 else 0):=by
  simp only [markedFamilyHubLoad,Finset.card_filter,Fin.sum_univ_castSucc]
  have hc (i:Fin n):=
    @Fin.snoc_castSucc n (fun _=>MarkedWheel tail head ktail khead m π b H₀ HK) B C i
  have hl:=
    @Fin.snoc_last n (fun _=>MarkedWheel tail head ktail khead m π b H₀ HK) B C
  apply congrArg₂ (·+·)
  · apply Finset.sum_congr rfl
    intro i hi
    rw [hc]
  · rw [hl]

end Oberwolfach
