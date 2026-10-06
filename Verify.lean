import Statement

open Schur

-- Trust base of the two main theorems.  The three non-kernel axioms should be
-- branchB0/1/2, one per verified branch; everything else is kernel-checked.
#print axioms Schur.four_colors_exact
#print axioms Schur.no_good_four_45

-- Readable restatements (no extra axioms).
#print axioms Schur.S4_statement
#print axioms Schur.S4_all_shorter

-- Kernel-only ingredients.
#print axioms Schur.searchB_spec
#print axioms Schur.exists_good_first_two
#print axioms Schur.exists_good_first_two_ok23
#print axioms Schur.ok23_disj
#print axioms Schur.searchB_false_of_three
#print axioms Schur.searchB_prefix_43
#print axioms Schur.c4_44_good_kernel

#check @Schur.four_colors_exact
#check @Schur.no_good_four_45
#check @Schur.S4_statement
