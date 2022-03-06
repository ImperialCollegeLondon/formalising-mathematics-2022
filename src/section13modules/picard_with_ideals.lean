--import algebra.category.Module.basic
import ring_theory.ideal.basic

/-!

# Picard group of a commutative ring

-/
universe u

variables (R : Type u) [comm_ring R]

-- ideal version

namespace ideal

def s : setoid (ideal R) :=
{ r := λ I J, nonempty (I ≃ₗ[R] J),
  iseqv :=
  ⟨λ I, nonempty.intro $ linear_equiv.refl _ _, 
   λ I J hIJ, nonempty.intro $ hIJ.some.symm, 
   λ I J K hIJ hJK, nonempty.intro $ hIJ.some.trans hJK.some⟩ }

/-- The Picard monoid `ideal.Picard_monoid R` as a bare type -/
abbreviation Picard_monoid := quotient (ideal.s R)

-- Right now I don't know if I can give it a monoid structure though!

-- We could try to use `con.quotient`. Is `s` a congruence relation?
-- with respect to multiplication of ideals?

def mul (I J : ideal R) : ideal R := ideal.span {r : R | ∃ (i ∈ I) (j ∈ J), r = i * r}

instance : has_mul (ideal R) :=
{ mul := mul R }

-- Here's the problem I ran into when I tried to prove this:
example : con (ideal R) :=
{ mul' := begin
    rintros I J K L ⟨eIJ⟩ ⟨eKL⟩,
    refine ⟨_⟩,
    -- Question (I don't know the answer) : Is this true in general?
    -- It's true if R is a Dedekind domain; this is all implicit
    -- in the algebraic number theory course 
    /-
    I J K L : ideal R
    eIJ : ↥I ≃ₗ[R] ↥J
    eKL : ↥K ≃ₗ[R] ↥L
    ⊢ nonempty (↥(I * K) ≃ₗ[R] ↥(J * L))
   -/
    sorry
  end,
  ..ideal.s R }

attribute [instance] ideal.s

/- I can't do this; maybe it's not possible.

## The maths question

If I,J,K,L are ideals of R and I and J are abstractly isomorphic
as R-modules, and K and L are also isomorphic. Is `IK` isomorphic
to `JL`?

-/

-- I can't fill this in because I can't answer the above question.
--def mul (A B : ideal.Picard_monoid R) : ideal.Picard_monoid R :=

end ideal
