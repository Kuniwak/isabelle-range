theory range imports Main begin

definition N :: "nat set" where
  "N == { x | x::nat. True }"

definition R :: "(nat \<times> nat) set" where
  "R == { (x, y) | x y. True }"

fun lower_bound :: "(nat \<times> nat) \<Rightarrow> nat" where
  "lower_bound (x, y) = x"

fun upper_bound :: "(nat \<times> nat) \<Rightarrow> nat" where
  "upper_bound (x, y) = y"

fun in_range :: "nat \<Rightarrow> (nat \<times> nat) \<Rightarrow> bool" where
  "in_range _ _ = True"

lemma example_3_8_in_R: "(3, 8) \<in> R"
  apply(unfold R_def)
  apply(rule CollectI)
  apply(rule_tac x=3 in exI)
  apply(rule_tac x=8 in exI)
  apply(rule conjI)
  apply(rule refl)
  apply(rule TrueI)
  done

lemma example_3_8_N: "\<forall>n::nat. in_range n (3, 8)"
  apply(subst in_range.simps)
  apply(rule allI)
  apply(rule TrueI)
  done

theorem example_3_8: "r = (3, 8) \<Longrightarrow>
  r \<in> R \<and>
  in_range 3 r \<and>
  in_range 4 r \<and>
  in_range 5 r \<and>
  in_range 6 r \<and>
  in_range 7 r \<and>
  in_range 8 r"
  apply(intro conjI)
  apply(erule ssubst)
  apply(rule example_3_8_in_R)
  apply(erule ssubst)
  apply(rule example_3_8_N[rule_format])
  apply(erule ssubst)
  apply(rule example_3_8_N[rule_format])
  apply(erule ssubst)
  apply(rule example_3_8_N[rule_format])
  apply(erule ssubst)
  apply(rule example_3_8_N[rule_format])
  apply(erule ssubst)
  apply(rule example_3_8_N[rule_format])
  apply(erule ssubst)
  apply(rule example_3_8_N[rule_format])
  done

theorem "r \<in> R \<Longrightarrow> \<exists>x. x = lower_bound r"
  apply(unfold R_def)
  apply(erule CollectE)
  apply(elim exE)
  apply(drule conjunct1)
  apply(erule ssubst)
  apply(subst lower_bound.simps)
  apply(rule_tac x=x in exI)
  apply(rule refl)
  done

theorem "r \<in> R \<Longrightarrow> \<exists>x. x = upper_bound r"
  apply(unfold R_def)
  apply(erule CollectE)
  apply(elim exE)
  apply(drule conjunct1)
  apply(erule ssubst)
  apply(subst upper_bound.simps)
  apply(rule_tac x=y in exI)
  apply(rule refl)
  done