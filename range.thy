theory range imports Main begin

definition N :: "nat set" where
  "N == { x | x::nat. True }"

definition R :: "(nat \<times> nat) set" where
  "R == { (x, y) | x y. True }"

fun lower_bound :: "(nat \<times> nat) \<Rightarrow> nat" where
  "lower_bound (x, y) = x"

theorem "r \<in> R \<Longrightarrow> lower_bound r \<in> N"
  apply(unfold R_def)
  apply(unfold N_def)
  apply(erule CollectE)
  apply(elim exE)
  apply(drule conjunct1)
  apply(erule ssubst)
  apply(subst lower_bound.simps)
  apply(rule CollectI)
  apply(rule_tac x=x in exI)
  apply(rule conjI)
  apply(rule refl)
  apply(rule TrueI)
  done

end