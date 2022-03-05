--import algebra.category.Module.basic
import ring_theory.ideal.basic

/-!

# Picard group of a commutative ring

-/
universe u

variables (R : Type u) [comm_ring R]

-- ideal version

def ideal.s : setoid (ideal R) :=
{ r := λ I J, nonempty (I ≃ₗ[R] J),
  iseqv :=
  ⟨λ I, nonempty.intro $ linear_equiv.refl _ _, 
   λ I J hIJ, nonempty.intro $ hIJ.some.symm, 
   λ I J K hIJ hJK, nonempty.intro $ hIJ.some.trans hJK.some⟩ }

def ideal.Picard_monoid := quotient (ideal.s R)


