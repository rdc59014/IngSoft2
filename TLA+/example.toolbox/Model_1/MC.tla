---- MODULE MC ----
EXTENDS example, TLC

\* Constant expression definition @modelExpressionEval
const_expr_155706132654873000 == 
CHOOSE y \in {1, 2, 3} : y*y = 4
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_155706132654873000>>)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_155706132655974000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_155706132656975000 ==
x /= 6
----
=============================================================================
\* Modification History
\* Created Sun May 05 10:02:06 ART 2019 by danilo
