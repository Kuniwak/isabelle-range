theory range imports Main begin

(* NLS-1 *)
definition R :: "(int \<times> int) set" where
  "R == { (x, y) | x y. x \<le> y }"

lemma le_le_trans: "\<lbrakk> a \<le> b; b \<le> c \<rbrakk> \<Longrightarrow> a \<le> c" for type a::int
  apply(rule leI)
  apply(rule notI)
  apply(drule_tac x=c and y=a and z=b in less_le_trans)
  apply(assumption)
  apply(drule_tac y=b in leD)
  apply(erule notE)
  apply(assumption)
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
  apply(unfold R_def)
  apply(intro allI)
  apply(rule ballI)
  apply(erule CollectE)
  apply(elim exE)
  apply(erule conjE)
  apply(erule ssubst)
  apply(subst in_range.simps)
  apply(rule_tac x="x \<le> n \<and> n \<le> y" in exI)
  apply(rule refl)
  done

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
  apply(subst lower_bound.simps)
  apply(rule refl)
  done

(* NLS-10 *)
theorem "upper_bound (3, 8) = 8"
  apply(subst upper_bound.simps)
  apply(rule refl)
  done

fun char_of_digit :: "nat \<Rightarrow> char" where
  c0: "char_of_digit 0 = CHR ''0''" |
  c1: "char_of_digit (Suc 0) = CHR ''1''" |
  c2: "char_of_digit (Suc (Suc 0)) = CHR ''2''" |
  c3: "char_of_digit (Suc (Suc (Suc 0))) = CHR ''3''" |
  c4: "char_of_digit (Suc (Suc (Suc (Suc 0)))) = CHR ''4''" |
  c5: "char_of_digit (Suc (Suc (Suc (Suc (Suc 0))))) = CHR ''5''" |
  c6: "char_of_digit (Suc (Suc (Suc (Suc (Suc (Suc 0)))))) = CHR ''6''" |
  c7: "char_of_digit (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) = CHR ''7''" |
  c8: "char_of_digit (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))) = CHR ''8''" |
  c9: "char_of_digit (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))) = CHR ''9''" |
  "char_of_digit _ = CHR ''?''"

fun string_of_nat :: "nat \<Rightarrow> string" where
  "string_of_nat i = (if i < 10
    then [char_of_digit i]
    else (string_of_nat (i div 10)) @ [char_of_digit (i mod 10)])"

fun string_of_int :: "int \<Rightarrow> string" where
  "string_of_int i = (if i > 0
    then string_of_nat (nat i)
    else (CHR ''-'') # (string_of_nat (nat \<bar>i\<bar>)))"

fun range_string :: "(int \<times> int) \<Rightarrow> string" where
  "range_string (a, b) = [CHR ''[''] @ (string_of_int a) @ [CHR '',''] @ (string_of_int b) @ [CHR '']'']"

(* NLS-3 *)
theorem stringify: "r \<in> R \<Longrightarrow> \<exists>s. s = range_string r"
  apply(unfold R_def)
  apply(erule CollectE)
  apply(elim exE)
  apply(erule conjE)
  apply(erule ssubst)
  apply(rule_tac x="range_string (x, y)" in exI)
  apply(rule refl)
  done

(* NLS-4 *)
theorem stringify_3_8: "range_string (3, 8) = ''[3,8]''"
  apply(unfold range_string.simps)
  apply(unfold string_of_int.simps)
  apply(simp)
  apply(rule conjI)
  apply(subgoal_tac "3 = (Suc (Suc (Suc 0)))")
  apply(erule ssubst)
  apply(rule c3)
  apply(simp)
  apply(subgoal_tac "8 = (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))")
  apply(erule ssubst)
  apply(rule c8)
  apply(simp)
  done

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

theorem range_eq_sym: "range_eq (a1, a2) (b1, b2) \<longleftrightarrow> range_eq (b1, b2) (a1, a2)"
  apply(subst range_eq.simps)
  apply(subst range_eq.simps)
  apply(rule iffI)
  apply(erule conjE)
  apply(erule subst)
  apply(erule subst)
  apply(rule conjI)
  apply(rule refl)
  apply(rule refl)
  apply(erule conjE)
  apply(erule subst)
  apply(erule subst)
  apply(rule conjI)
  apply(rule refl)
  apply(rule refl)
  done

lemma all_iffD: "(\<forall>x. P x \<longleftrightarrow> Q x) \<Longrightarrow> (\<forall>x. P x \<longrightarrow> Q x) \<and> (\<forall>x. Q x \<longrightarrow> P x)"
  apply(rule conjI)
  apply(rule allI)
  apply(erule_tac x=x in allE)
  apply(erule iffE)
  apply(assumption)
  apply(rule allI)
  apply(erule_tac x=x in allE)
  apply(erule iffE)
  apply(assumption)
  done

lemma range_uniq: "\<lbrakk> a1 \<le> a2; b1 \<le> b2; \<forall>n. (a1 \<le> n \<and> n \<le> a2) \<longleftrightarrow> (b1 \<le> n \<and> n \<le> b2) \<rbrakk> \<Longrightarrow> a1 = b1 \<and> a2 = b2" for a1::int and a2::int and b1::int and b2::int
  apply(drule all_iffD)
  apply(erule conjE)
  apply(rule conjI)
  apply(erule_tac x=a1 in allE)
  apply(erule impE)
  apply(rule conjI)
  apply(rule order_refl)
  apply(assumption)
  apply(erule conjE)
  apply(erule_tac x=b1 in allE)
  apply(erule impE)
  apply(rule conjI)
  apply(rule order_refl)
  apply(assumption)
  apply(erule conjE)
  apply(erule antisym)
  apply(assumption)
  apply(erule_tac x=a2 in allE)
  apply(erule impE)
  apply(erule conjI)
  apply(rule order_refl)
  apply(erule_tac x=b2 in allE)
  apply(erule impE)
  apply(erule conjI)
  apply(rule order_refl)
  apply(elim conjE)
  apply(erule antisym)
  apply(assumption)
  done

theorem in_range_uniq: "\<forall>r1 \<in> R. \<forall>r2 \<in> R.
    r1 = (a1, a2) \<and> r2 = (b1, b2)
    \<longrightarrow> (\<forall>n. in_range n (a1, a2) \<longleftrightarrow> in_range n (b1, b2))
    \<longrightarrow> range_eq (a1, a2) (b1, b2)"
  apply(unfold R_def)
  apply(subst range_eq.simps)
  apply(subst in_range.simps)
  apply(subst in_range.simps)
  apply(intro ballI)
  apply(intro impI)
  apply(elim conjE)
  apply(drule_tac a=r1 and b="(a1, a2)" in back_subst)
  apply(assumption)
  apply(drule_tac a=r2 and b="(b1, b2)" in back_subst)
  apply(assumption)
  apply(elim CollectE)
  apply(elim exE)
  apply(elim conjE)
  apply(elim Pair_inject)
  apply(drule_tac a=a1 and b=x and c=y in ord_eq_le_trans)
  apply(assumption)
  apply(drule_tac a=a1 and b=y and c=a2 in ord_le_eq_trans)
  apply(erule sym)
  apply(drule_tac a=b1 and b=xa and c=ya in ord_eq_le_trans)
  apply(assumption)
  apply(drule_tac a=b1 and b=ya and c=b2 in ord_le_eq_trans)
  apply(erule sym)
  apply(erule range_uniq)
  apply(assumption)
  apply(assumption)
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

theorem range_contains_antisym: "range_contains (a1, a2) (b1, b2) \<and> range_contains (b1, b2) (a1, a2) \<longleftrightarrow> range_eq (a1, a2) (b1, b2)"
  apply(subst range_contains.simps)
  apply(subst range_contains.simps)
  apply(subst range_eq.simps)
  apply(rule iffI)
  apply(elim conjE)
  apply(rule conjI)
  apply(erule antisym)
  apply(assumption)
  apply(erule_tac x=a2 in antisym)
  apply(assumption)
  apply(erule conjE)
  apply(rule conjI)
  apply(erule subst)
  apply(erule subst)
  apply(rule conjI)
  apply(rule order_refl)
  apply(rule order_refl)
  apply(erule subst)
  apply(erule subst)
  apply(rule conjI)
  apply(rule order_refl)
  apply(rule order_refl)
  done