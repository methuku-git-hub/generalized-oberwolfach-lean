module

public import Oberwolfach.MarkedRootPair

@[expose] public section

/-! Enlarging the forbidden hub set leaves both root graphs and their
representation maps unchanged. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
variable {V U E K A S:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b m:ℕ}

def MarkedRootPair.enlargeBase
    (G:MarkedRootPair tail head ktail khead H₀ HK π b m A S)
    (B:Finset U) (hB:G.B⊆B):MarkedRootPair tail head ktail khead H₀ HK π b m A S:=
  {G with B:=B,hubRoots:=fun s=>⟨hB (G.hubRoots s).1,hB (G.hubRoots s).2⟩}

@[simp] theorem MarkedRootPair.enlargeBase_source
    (G:MarkedRootPair tail head ktail khead H₀ HK π b m A S)
    (B:Finset U) (hB:G.B⊆B):(G.enlargeBase B hB).source=G.source:=rfl
@[simp] theorem MarkedRootPair.enlargeBase_image
    (G:MarkedRootPair tail head ktail khead H₀ HK π b m A S)
    (B:Finset U) (hB:G.B⊆B):(G.enlargeBase B hB).image=G.image:=rfl

end Oberwolfach
