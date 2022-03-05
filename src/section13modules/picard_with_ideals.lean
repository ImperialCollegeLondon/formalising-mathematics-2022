--import algebra.category.Module.basic
import ring_theory.ideal.basic

/-!

# Picard group of a commutative ring

-/
universe u

variables (R : Type u) [comm_ring R]

-- ideal version

def ideal.s : setoid (ideal R) :=
{ r := λ I J, nonempty (I ≃ₗ[R] I),
  iseqv := begin
    refine ⟨_, _, _⟩,
    { intro x,
      exact has_one.nonempty, },
    { intros x y h,
      exact has_one.nonempty, },
    { intros x y z h1 h2,
      exact has_one.nonempty, }
  end }

def ideal.Picard_monoid := quotient (ideal.s R)
 
#exit


