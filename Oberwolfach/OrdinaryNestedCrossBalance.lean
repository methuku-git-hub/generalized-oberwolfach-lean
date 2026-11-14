module

public import Oberwolfach.OrdinaryCrossBalanceChange

@[expose] public section
/-! Remove a nested deep pair using its cross-balance, instead of charging
its full cardinality on the outer pair. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_nested_cross_balance
    {V U:Type} [DecidableEq V] [DecidableEq U]
    (A A₀ X T:Finset V) (B B₀ Z W:Finset U) (b deep L:ℝ)
    (hTX:T⊆X) (hWZ:W⊆Z)
    (hbase:|((A₀∩X).card:ℝ)-2*(B₀∩Z).card|≤b)
    (hdeep:|((A∩T).card:ℝ)-2*(B∩W).card|≤deep)
    (hr:((changed A A₀).card:ℝ)≤L)
    (hs:((changed B B₀).card:ℝ)≤L):
    |((A∩(X\T)).card:ℝ)-2*(B∩(Z\W)).card|≤b+3*L+deep:=by
  have hb:=abs_le.mp (ordinary_cross_balance_change A A₀ X B B₀ Z b L hbase hr hs)
  have hd:=abs_le.mp hdeep
  have hleft:((A∩(X\T)).card:ℝ)+(A∩T).card=(A∩X).card:=by
    have he:(A∩X)\T=A∩(X\T):=by ext x;simp [and_assoc]
    have hi:(A∩X)∩T=A∩T:=by ext x;simp only [Finset.mem_inter];constructor <;> intro h <;> aesop
    have hh:=Finset.card_sdiff_add_card_inter (A∩X) T
    rw [he,hi] at hh
    exact_mod_cast hh
  have hright:((B∩(Z\W)).card:ℝ)+(B∩W).card=(B∩Z).card:=by
    have he:(B∩Z)\W=B∩(Z\W):=by ext x;simp [and_assoc]
    have hi:(B∩Z)∩W=B∩W:=by ext x;simp only [Finset.mem_inter];constructor <;> intro h <;> aesop
    have hh:=Finset.card_sdiff_add_card_inter (B∩Z) W
    rw [he,hi] at hh
    exact_mod_cast hh
  apply abs_le.mpr
  constructor <;> linarith only [hb.1,hb.2,hd.1,hd.2,hleft,hright]
end Oberwolfach
