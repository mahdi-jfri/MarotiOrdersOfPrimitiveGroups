module

public import Maroti.Classical.AutBound
public import Maroti.Classical.SymplecticOrderBound
public import Maroti.Classical.SymplecticHeisenberg
public import Maroti.Symplectic.SmallEven
public import Maroti.SymplecticSmall.PSp62
public import Maroti.SymplecticSmall.SylowSeventeen
public import Maroti.Unitary.Heisenberg
public import Maroti.Orthogonal.OrderBound
public import Maroti.Orthogonal.Small

/-!
# The classical groups other than `PSL`

This file collects the classical families other than `PSL(n, q)` into one statement for Step 2
of Maróti's proof (A. Maróti, *On the orders of primitive groups*, J. Algebra 258 (2002),
Section 2, page 634).

The symplectic groups are split by the parity of `q`. For odd `q` the bound is
`symplecticCase_odd`. For even `q` it is `symplecticCase_even_of_small`, which needs three facts
about small groups: every proper subgroup of `PSp(6, 2)` has index at least 23
(`index_ge_pSp_six_two`), no subgroup of `PSp(4, 4)` has index 24
(`index_ne_twentyFour_pSp_four_four`), and no subgroup of `PSp(8, 2)` has index between 56 and 63
(`not_index_mem_pSp_eight_two`). The unitary and orthogonal groups have one theorem each.
-/

@[expose] public section

namespace Maroti

/-- Maróti's bound for primitive almost simple groups whose socle is a symplectic group
`PSp(2n, q)` (Maróti, Section 2, Step 2, page 634). -/
theorem symplecticCase : AlmostSimpleCase (ClassicalSocle .PSp) :=
  symplecticCase_of_parity symplecticCase_odd
    (symplecticCase_even_of_small index_ge_pSp_six_two index_ne_twentyFour_pSp_four_four
      fun S _ hS H h56 h63 => not_index_mem_pSp_eight_two S hS H h56 h63)

/-- Maróti's bound for primitive almost simple groups whose socle is a classical group other
than `PSL(n, q)` (Maróti, Section 2, Step 2, page 634). -/
theorem otherClassicalCase : AlmostSimpleCase OtherClassicalSocle :=
  otherClassicalCase_of_tags unitaryCase symplecticCase orthogonalOddCase orthogonalPlusCase
    orthogonalMinusCase

end Maroti
