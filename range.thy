theory range imports Main begin

definition R :: "(nat \<times> nat) set" where
  "R == { (x, y) | x y. x \<le> y }"

lemma eq_le_le1: "(c::nat) = a \<longrightarrow> a \<le> b \<longrightarrow> c \<le> a"
  apply(intro impI)
  apply(erule subst)
  apply(rule eq_refl)
  apply(rule refl)
  done

lemma eq_le_le2: "(c::nat) = a \<longrightarrow> b \<le> a \<longrightarrow> b \<le> c"
  apply(intro impI)
  apply(erule ssubst)
  apply(assumption)
  done

lemma le_le_trans: "(a::nat) \<le> b \<longrightarrow> b \<le> c \<longrightarrow> a \<le> c"
  apply(intro impI)
  apply(case_tac "a=b")
  apply(erule ssubst)
  apply(assumption)
  apply(drule_tac a=a and b=b in le_neq_trans)
  apply(assumption)
  apply(case_tac "b=c")
  apply(drule_tac x=a and y=b and z=c in less_le_trans)
  apply(assumption)
  apply(erule less_imp_le)
  apply(drule le_neq_trans)
  apply(assumption)
  apply(drule_tac x=a and y=b and z=c in less_trans)
  apply(assumption)
  apply(erule less_imp_le)
  done

theorem "a > b \<Longrightarrow> (a, b) \<notin> R"
  apply(unfold R_def)
  apply(rule notI)
  apply(erule CollectE)
  apply(elim exE)
  apply(erule conjE)
  apply(erule Pair_inject)
  apply(drule_tac a=x and b=y in eq_le_le1[rule_format])
  apply(assumption)
  apply(drule sym)
  apply(drule_tac a=x and b=y and c=b in ord_le_eq_trans)
  apply(assumption)
  apply(drule_tac a=a and b=x and c=b in le_le_trans[rule_format])
  apply(assumption)
  apply(drule_tac y=a in leD)
  apply(erule notE)
  apply(assumption)
  done

fun lower_bound :: "(nat \<times> nat) \<Rightarrow> nat" where
  "lower_bound (x, y) = x"

fun upper_bound :: "(nat \<times> nat) \<Rightarrow> nat" where
  "upper_bound (x, y) = y"

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

fun in_range :: "nat \<Rightarrow> (nat \<times> nat) \<Rightarrow> bool" where
  "in_range n (x, y) = ((x \<le> n) \<and> (n \<le> y))"

lemma example_3_8_in_R: "(3, 8) \<in> R"
  apply(unfold R_def)
  apply(rule CollectI)
  apply(rule_tac x=3 in exI)
  apply(rule_tac x=8 in exI)
  apply(rule conjI)
  apply(rule refl)
  apply(simp)
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
  apply(subst in_range.simps)
  apply(rule conjI)
  apply(rule eq_imp_le)
  apply(rule refl)
  apply(rule less_imp_le_nat)
  apply(auto)
  done

theorem example_3_8_w: "\<lbrakk> r = (3, 8); E = { x | x. 3 \<le> x \<and> x \<le> 8 } \<rbrakk> \<Longrightarrow>
  (\<forall>n \<in> E. in_range n r) \<and> (\<forall>n::nat. n \<notin> E \<longrightarrow> \<not>in_range n r)"
  apply(elim ssubst)
  apply(rule conjI)
  apply(rule ballI)
  apply(erule CollectE)
  apply(erule exE)
  apply(erule conjE)
  apply(erule ssubst)
  apply(subst in_range.simps)
  apply(assumption)
  apply(rule allI)
  apply(rule impI)
  apply(rule notI)
  apply(erule in_range.elims)
  apply(erule notE)
  apply(erule ssubst)
  apply(erule Pair_inject)
  apply(erule conjE)
  apply(rule CollectI)
  apply(rule_tac x=na in exI)
  apply(intro conjI)
  apply(rule refl)
  apply(drule_tac c=3 and a=x and b=na in eq_le_le1[rule_format])
  apply(assumption)
  apply(erule_tac a=3 and b=x and c=na in le_le_trans[rule_format])
  apply(assumption)
  apply(erule_tac c=8 and a=y and b=na in eq_le_le2[rule_format])
  apply(assumption)
  done

fun range_eq :: "(nat \<times> nat) \<Rightarrow> (nat \<times> nat) \<Rightarrow> bool" where
  "range_eq (a1, a2) (b1, b2) = ((a1 = b1) \<and> (a2 = b2))"

theorem "range_eq (a1, a2) (b1, b2) \<Longrightarrow> \<forall>n::nat. in_range n (a1, a2) \<longleftrightarrow> in_range n (b1, b2)"
  apply(erule range_eq.elims)
  apply(rule allI)
  apply(erule conjE)
  apply(elim Pair_inject)
  apply(drule_tac r=a1 and s=a1a and t=b1a in trans)
  apply(assumption)
  apply(drule_tac r=a1 and s=b1a and t=b1 in trans_sym)
  apply(assumption)
  apply(drule_tac r=a2 and s=a2a and t=b2a in trans)
  apply(assumption)
  apply(drule_tac r=a2 and s=b2a and t=b2 in trans_sym)
  apply(assumption)
  apply(erule_tac t=b1 and s=a1 in subst)
  apply(erule_tac t=b2 and s=a2 in subst)
  apply(rule refl)
  done