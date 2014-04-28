module RSDF
where


type RSDF a = ()

--%BEGING
--S = Main S2.
--Main m = Filter Nz M.
--If a b pm = case 6 pm a b err err err err.
--Nz pm = case 6 pm err err false true err err.
--Filter p pm = case 6 pm err err err err nil (If (cons X (Filter p XS)) (Filter p XS) (p X)).

--S2 = ListN.
--N = z.
--N = s N.
--ListN = nil.
--ListN = cons N ListN.
--%ENDG

--%BEGINA
--q0 cons -> q1 q0.
--q1 z ->.
--%ENDA

fromWPMRS :: PMRS () -> RSDF ()
fromWPMRS = undefined