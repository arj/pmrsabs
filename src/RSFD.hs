module RSDF
where

type RSDFRule a = RSDFRule {
	rsdfRuleHead :: SortedSymbol a
  , rsdfRuleVars :: [String]
  , ruleBody     :: Term a
}

type RSFDRules a = MultiMap (SortedSymbol a) (RSFDRule a)

type RSFD a = RSFD { rsfdTerminals :: RankedAlphabet a
  , rsfdNonterminals :: RankedAlphabet a
  , rsfdData :: Set String
  , rsfdRules :: RSFDRules a
  , rsfdStart :: SortedSymbol a
}

instance Show a => Show (RSFD a) where
	show (RSFD sigma n d r s) = "<" ++ (intercalate ",\n" [showSet t,showSet nt,show $ concat $ MM.elems r,show s]) ++ ">"

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

-- Steps:
-- (0. Flatten pattern matching?)
--  1. Create finite data domain D from Sigma
--     We only need the terminal symbols that are actually
--     used in the pattern matching part of the symbols.
--  2. Transform all pattern matching rules to normal
--     rules with case statement. And combine
--     several rules into one, e.g.
--     Filter p nil -> t1 and Filter p (cons _ _) -> t2
--     must be combined to Filter p d -> case(d,t1,t2)
--  3. d must be of type d, thus we have to ensure that
--     the calls to filter only use elements of d.
--     Enforce this by an analysis and transformation.
--     We probably only need depth 1 as case cannot look deeper.
--  4. CPS transformation if necessary? We cannot return values
--     of type d!


fromWPMRS :: PMRS () -> RSDF ()
fromWPMRS = undefined