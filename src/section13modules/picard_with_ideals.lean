--import algebra.category.Module.basic
import ring_theory.ideal.basic
import linear_algebra.tensor_product

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

-- However perhaps we can still define the Picard group.
-- Let's stick to invertible ideals.

-- notation
open_locale tensor_product

variable {R}

def are_tensor_inverses (I J : ideal R) : Prop :=
nonempty (I ⊗[R] J ≃ₗ[R] R)

lemma are_tensor_inverses.symm {I J : ideal R} (e : are_tensor_inverses I J) :
  are_tensor_inverses J I :=
nonempty.map (λ i, linear_equiv.trans (tensor_product.comm R _ _) i) e

def is_tensor_invertible (I : ideal R) : Prop := 
∃ J : ideal R, nonempty (I ⊗[R] J ≃ₗ[R] R)

namespace is_tensor_invertible

variable (I : ideal R)

lemma tensor_iso_prod (h : is_tensor_invertible I) (K : ideal R) :
  nonempty (K ⊗[R] I ≃ (K * I : ideal R)) :=
begin
  -- Antoine said this might be some standard fact about
  -- invertible ideals
  sorry
end 

variable (R)

abbreviation bundled_tensor_invertible_ideals := {I : ideal R // is_tensor_invertible I}

instance s : setoid (bundled_tensor_invertible_ideals R) :=
{ r := λ I J, nonempty (I.1 ≃ₗ[R] J.1),
  iseqv := 
  ⟨λ I, nonempty.intro $ linear_equiv.refl _ _,  
   λ I J, nonempty.map linear_equiv.symm,
   λ I J K, nonempty.map2 linear_equiv.trans⟩ }

def mul (I J : bundled_tensor_invertible_ideals R) : bundled_tensor_invertible_ideals R :=
⟨I.1 * J.1, sorry⟩ -- product of tensor-invertible ideals is invertible

end is_tensor_invertible


end ideal
