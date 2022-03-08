import tactic -- for the tactics
import ring_theory.ideal.operations -- for the ideals
-- (including product of ideals)

-- universe variable
universe u

variables (R : Type u) [comm_ring R]

-- let V be a vector space over R (i.e. a module over R)
variables (V : Type u) [add_comm_group V]
  [module R V]
  
-- the R-linear isomorphism `V ≃ₗ[R] V`
#check linear_equiv.refl R V
-- linear_equiv.refl R V : V ≃ₗ[R] V

-- Note that this isn't the true-false statement "V is isomorphic to V",
-- it's the actual identity isomorphism V ≃ V.

#check nonempty

namespace ideal

def s (R : Type u) [comm_ring R] : setoid (ideal R) :=
{ r := λ I J, nonempty (I ≃ₗ[R] J),
  iseqv := begin
    refine ⟨_, _, _⟩,
    { intro K,
      exact nonempty.intro (linear_equiv.refl R K) },
    { rintros I J ⟨hIJ⟩,
      exact nonempty.intro hIJ.symm },
    { rintros I J K ⟨hIJ⟩ ⟨hJK⟩,
      exact nonempty.intro (hIJ.trans hJK) },
  end }

-- not done in class

set_option pp.proofs true

#check submodule.map_mul
def linear_map.rmul (I : ideal R) {J K : ideal R} (e : J →ₗ[R] K) : 
  (J * I : ideal R) →ₗ[R] (K * I : ideal R) := 
{ to_fun := λ x, ⟨e.to_fun ⟨x.1, ideal.mul_le_right x.2⟩, begin
  cases x with x hx,
  dsimp, -- looks like hx isn't in the goal
  -- but set_option pp.proofs true and you'll see it hidden there
  have h2 : x ∈ J := mul_le_right hx,
  rw show mul_le_right hx = h2, from rfl,
  -- now it's gone
  revert h2,
  rw submodule.mul_eq_span_mul_set at hx,
  apply submodule.span_induction hx,
  let xJ : J := ⟨x, h2⟩,
  change ↑(e xJ) ∈ K * I,
  refine submodule.span_induction' _ _ _ _ hx; clear x,
  { rintro - ⟨r, s, hr, hs, rfl⟩,
    
  
  }
end⟩,
  map_add' := sorry,
  map_smul' := sorry }




-- not done in class


-/
-- I didn't do `mul'` in class
def s_con : con (ideal R) :=
{ mul' := begin
    rintros I J K L ⟨eIJ⟩ ⟨eKL⟩,
    let eIKJK : (I * K : ideal R) ≃ₗ[R] (J * K : ideal R),
    sorry,
    sorry, -- tricky exercise!
end,
  ..ideal.s R,
   }

-- quotienting out by the congruence relation
abbreviation Picard_monoid := (s_con R).quotient

-- and because we used `con.quotient` the quotient
-- gets a monoid instance automatically
instance : monoid (Picard_monoid R) := infer_instance

abbreviation Picard_group := units (Picard_monoid R)

end ideal

-- the Picard group of a commutative ring is a group
instance : group (ideal.Picard_group R) := by apply_instance 

