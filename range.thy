theory range imports Main begin

(* NLS-1 *)
definition R :: "(int \<times> int) set" where
  "R == { (x, y) | x y. x \<le> y }"

lemma le_le_trans[rule_format]: "a \<le> b \<longrightarrow> b \<le> c \<longrightarrow> a \<le> c" for type a::int
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

(* NLS-5 *)
theorem "a > b \<Longrightarrow> (a, b) \<notin> R"
  apply(unfold R_def)
  apply(rule notI)
  apply(erule CollectE)
  apply(elim exE)
  apply(erule conjE)
  apply(erule Pair_inject)
  apply(drule_tac eq_refl)
  apply(drule sym)
  apply(drule_tac a=x and b=y and c=b in ord_le_eq_trans)
  apply(assumption)
  apply(drule_tac a=a and b=x and c=b in le_le_trans)
  apply(assumption)
  apply(drule_tac y=a in leD)
  apply(erule notE)
  apply(assumption)
  done

fun lower_bound :: "(int \<times> int) \<Rightarrow> int" where
  "lower_bound (x, y) = x"

fun upper_bound :: "(int \<times> int) \<Rightarrow> int" where
  "upper_bound (x, y) = y"

(* NLS-2 *)
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

(* NLS-2 *)
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

fun in_range :: "int \<Rightarrow> (int \<times> int) \<Rightarrow> bool" where
  "in_range n (x, y) = (x \<le> n \<and> n \<le> y)"

(* NLS-6 *)
theorem "\<forall>n. \<forall>r \<in> R. \<exists>b. b = in_range n r"
  oops

(* NLS-9 *)
lemma example_3_8_in_R: "(3, 8) \<in> R"
  apply(unfold R_def)
  apply(rule CollectI)
  apply(rule_tac x=3 in exI)
  apply(rule_tac x=8 in exI)
  apply(rule conjI)
  apply(rule refl)
  apply(simp)
  done

(* NLS-10 *)
theorem "lower_bound (3, 8) = 3"
  oops

(* NLS-10 *)
theorem "upper_bound (3, 8) = 8"
  oops

(* NLS-11, NLS-12 *)
theorem example_3_8: "\<lbrakk> r = (3, 8); E = { x | x. 3 \<le> x \<and> x \<le> 8 } \<rbrakk> \<Longrightarrow>
    \<forall>n. n \<in> E \<longleftrightarrow> in_range n r"
  apply(elim ssubst)
  apply(subst in_range.simps)
  apply(rule allI)
  apply(rule iffI)
  apply(erule CollectE)
  apply(erule exE)
  apply(erule conjE)
  apply(erule ssubst)
  apply(assumption)
  apply(rule CollectI)
  apply(rule_tac x=n in exI)
  apply(rule conjI)
  apply(rule refl)
  apply(assumption)
  done

fun range_eq :: "(int \<times> int) \<Rightarrow> (int \<times> int) \<Rightarrow> bool" where
  "range_eq (a1, a2) (b1, b2) = (a1 = b1 \<and> a2 = b2)"

(* NLS-7 *)
theorem "range_eq (a1, a2) (b1, b2) \<Longrightarrow>
    \<forall>n. in_range n (a1, a2) \<longleftrightarrow> in_range n (b1, b2)"
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

fun range_contains :: "(int \<times> int) \<Rightarrow> (int \<times> int) \<Rightarrow> bool" where
  "range_contains (a1, a2) (b1, b2) = (a1 \<le> b1 \<and> b2 \<le> a2)"

(* NLS-8 *)
theorem "range_contains (a1, a2) (b1, b2) \<Longrightarrow>
    \<forall>n. in_range n (b1, b2) \<longrightarrow> in_range n (a1, a2)"
  apply(unfold in_range.simps)
  apply(erule range_contains.elims)
  apply(elim Pair_inject)
  apply(rule allI)
  apply(rule impI)
  apply(elim conjE)
  apply(rule conjI)
  apply(erule ssubst)
  apply(drule_tac s=b2 in sym)
  apply(drule_tac s=b1 in sym)
  apply(drule_tac x=b1a in eq_refl)
  apply(erule_tac a=a1 and b=b1a and c=n in le_le_trans)
  apply(erule_tac b=b1 and c=n in le_le_trans)
  apply(assumption)
  apply(drule_tac s=b2 in sym)
  apply(drule_tac s=b2 and P="\<lambda>b2. n \<le> b2" in ssubst)
  apply(assumption)
  apply(drule_tac a=n and b=b2a and c=a2a in le_le_trans)
  apply(assumption)
  apply(erule_tac t=a2 in ssubst)
  apply(assumption)
  done