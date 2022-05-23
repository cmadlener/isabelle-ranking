theory Ranking_Probabilistic
  imports
    Ranking
    "HOL-Probability.Random_Permutations"
    "HOL-Probability.Product_PMF"
    "Monad_Normalisation.Monad_Normalisation"
begin

no_syntax
  "_maplet"  :: "['a, 'a] \<Rightarrow> maplet"             ("_ /\<mapsto>/ _")
  "_maplets" :: "['a, 'a] \<Rightarrow> maplet"             ("_ /[\<mapsto>]/ _")
  ""         :: "maplet \<Rightarrow> maplets"             ("_")
  "_Maplets" :: "[maplet, maplets] \<Rightarrow> maplets" ("_,/ _")
  "_MapUpd"  :: "['a \<rightharpoonup> 'b, maplets] \<Rightarrow> 'a \<rightharpoonup> 'b" ("_/'(_')" [900, 0] 900)
  "_Map"     :: "maplets \<Rightarrow> 'a \<rightharpoonup> 'b"            ("(1[_])")

no_syntax (ASCII)
  "_maplet"  :: "['a, 'a] \<Rightarrow> maplet"             ("_ /|->/ _")
  "_maplets" :: "['a, 'a] \<Rightarrow> maplet"             ("_ /[|->]/ _")

no_translations
  "_MapUpd m (_Maplets xy ms)"  \<rightleftharpoons> "_MapUpd (_MapUpd m xy) ms"
  "_MapUpd m (_maplet  x y)"    \<rightleftharpoons> "m(x := CONST Some y)"
  "_Map ms"                     \<rightleftharpoons> "_MapUpd (CONST empty) ms"
  "_Map (_Maplets ms1 ms2)"     \<leftharpoondown> "_MapUpd (_Map ms1) ms2"
  "_Maplets ms1 (_Maplets ms2 ms3)" \<leftharpoondown> "_Maplets (_Maplets ms1 ms2) ms3"

lemma bounded_by_sum_bounds_sum_aux:
  fixes x :: "nat \<Rightarrow> real"
  assumes "n > 0"
  assumes "1 - x (Suc t) \<le> 1/n * (\<Sum>s\<le>Suc t. x s)"
  shows "(\<Sum>s\<le>(Suc t). x s) \<ge> (1+(\<Sum>s\<le>t. x s)) / (1 + 1/n)"
  using assms
proof -
  from assms have "1 + (\<Sum>s\<le>t. x s) \<le> (\<Sum>s\<le>Suc t. x s) + 1/n * (\<Sum>s\<le>Suc t. x s)"
    by fastforce

  then have "1 + (\<Sum>s\<le>t. x s) \<le> (\<Sum>s\<le>Suc t. x s) * (1 + 1/n)"
    by argo

  with assms show ?thesis
    by (auto intro!: mult_imp_div_pos_le simp: add_pos_pos)
qed

lemma bounded_by_sum_bounds_sum:
  fixes x :: "nat \<Rightarrow> real"
  assumes "\<And>t. t < n \<Longrightarrow> 1 - x t \<le> 1/n * (\<Sum>s\<le>t. x s)"
  assumes "1 - 1/(n+1) \<le> x 0"
  assumes "t < (n::nat)"
  assumes "0 < n"
  shows "(\<Sum>s\<le>t. x s) \<ge> (\<Sum>s\<le>t. (1 - 1/(n+1))^(s+1))"
  using assms
proof (induction t)
  case 0
  then show ?case
    by simp
next
  case (Suc t)

  then have IH: "(\<Sum>s\<le>t. x s) \<ge> (\<Sum>s\<le>t. (1-1/(real n+1))^(s+1))"
    by (auto intro: Suc.IH)

  from Suc have bound_rewrite_sum: "(\<Sum>s\<le>Suc t. x s) \<ge> (1+(\<Sum>s\<le>t. x s)) / (1+1/n)"
    by (intro bounded_by_sum_bounds_sum_aux) simp

  have "(1+(\<Sum>s\<le>t. x s)) / (1+1/n) = (1 - 1/(n+1)) * (1 + (\<Sum>s\<le>t. x s))" (is "?LHS = _")
    using \<open>n > 0\<close>
    by (simp add: field_simps)

  also have "\<dots> = (1 - 1/(n+1)) + (1-1/(n+1)) * (\<Sum>s\<le>t. x s)"
    by argo

  also have "\<dots> \<ge> (1-1/(n+1)) + (1-1/(n+1))*(\<Sum>s\<le>t. (1-1/(real n+1))^(s+1))" (is "_ \<ge> ?S2")
    using IH
    by (auto intro: add_left_mono mult_left_mono)

  finally have IH_applied: "?LHS \<ge> ?S2" .

  have "?S2 = (1-1/(n+1)) + (\<Sum>s\<le>t. (1-1/(n+1))^(s+2))"
    by (auto simp: sum_distrib_left field_simps)

  also have "\<dots> = (1-1/(n+1)) + (\<Sum>s\<in>{0+1..t+1}. (1-1/(n+1))^(s+1))"
    by (subst sum.atLeastAtMost_shift_bounds)
       (auto simp: atLeast0AtMost)

  also have "\<dots> = (1-1/(n+1)) + (\<Sum>s=Suc 0..Suc t. (1-1/(n+1))^(s+1))"
    by simp


  also have "\<dots> = (1-1/(n+1))^(0+1) + (\<Sum>s=Suc 0..Suc t. (1-1/(n+1))^(s+1))"
    by simp

  also have "\<dots> = (\<Sum>s\<le>Suc t. (1-1/(n+1))^(s+1))" (is "_ = ?RHS")
    apply (simp add: sum.atMost_shift)
    apply (cases t)
     apply simp
    apply (simp only: sum.atLeast_Suc_atMost_Suc_shift)
    apply (simp del:  sum.lessThan_Suc add: atLeast0AtMost lessThan_Suc_atMost)
    done

  finally have final: "?S2 = ?RHS" .

  show ?case 
    apply (intro order_trans[OF _ bound_rewrite_sum] ord_eq_le_trans[OF _ IH_applied])
    apply (subst final)
    apply (simp add: ac_simps)
    done
qed

lemma sum_gp_strict_Suc: "(\<Sum>s<n. (1 - 1/(n+1))^(s+1)) = n - n*(n/(n+1))^n"
  apply (auto simp flip: sum_distrib_left simp: sum_gp_strict)
  apply (auto simp add: field_split_simps)
  by (metis distrib_right mult_1 nat.simps(3) of_nat_Suc of_nat_eq_0_iff power.simps(2) power_eq_0_iff)

lemma permutation_move_to:
  assumes "\<sigma> \<in> permutations_of_set V"
  assumes "v \<in> V"
  shows "\<sigma>[v \<mapsto> t] \<in> permutations_of_set V"
  using assms
  by (metis move_to_distinct move_to_set_eq permutations_of_setD(1) permutations_of_setD(2) permutations_of_setI)

lemma move_to_eq_unique_vertex:
  assumes "\<sigma>' \<in> permutations_of_set V"
  assumes "\<sigma> \<in> permutations_of_set V"
  assumes "index \<sigma> v = t" "v \<in> V"
  assumes "\<sigma> = \<sigma>'[w \<mapsto> t]"
  shows "v = w"
  using assms
  by (metis distinct_card index_eq_index_conv index_less_size_conv move_to_index_v permutations_of_setD)

lemma permutations_move_to_eq_iff:
  assumes "\<sigma> \<in> permutations_of_set V"
  assumes "t < length \<sigma>"
  assumes "\<sigma>' \<in> permutations_of_set V"
  shows "card (V \<inter> {v. \<sigma> = \<sigma>'[v \<mapsto> t]}) = 1 \<longleftrightarrow> [x <- \<sigma>'. x \<noteq> (THE v. index \<sigma> v = t)] = [x <- \<sigma>. x \<noteq> (THE v. index \<sigma> v = t)]"
proof (rule iffI)
  assume card_1: "card (V \<inter> {v. \<sigma> = \<sigma>'[v \<mapsto> t]}) = 1"
  with assms  obtain w where w: "w \<in> V" "\<sigma> = \<sigma>'[w \<mapsto> t]"
    by (smt (verit) card.empty disjoint_iff_not_equal mem_Collect_eq zero_neq_one)

  with card_1 assms have filter_eq: "[x <- \<sigma>'. x \<noteq> w] = [x <- \<sigma>. x \<noteq> w]"
    by (auto intro!: distinct_order_filter_eq dest: permutations_of_setD permutation_move_to
             simp: distinct_move_to_indices_if_eq)

  from w card_1 assms have "(THE v. index \<sigma> v = t) = w"
    apply (auto intro!: the_equality move_to_index_v dest: permutations_of_setD
      simp: length_finite_permutations_of_set)
    by (metis assms(2) index_less_size_conv move_to_eq_unique_vertex permutations_of_setD(1))

  with filter_eq show "[x <- \<sigma>'. x \<noteq> (THE v. index \<sigma> v = t)] = [x <- \<sigma>. x \<noteq> (THE v. index \<sigma> v = t)]"
    by blast
next
  assume filter_eq: "[x <- \<sigma>'. x \<noteq> (THE v. index \<sigma> v = t)] = [x <- \<sigma>. x \<noteq> (THE v. index \<sigma> v = t)]"

  from assms obtain v where v: "index \<sigma> v = t" "v \<in> V"
    by (metis index_nth_id nth_mem permutations_of_setD(1) permutations_of_setD(2))

  with \<open>t < length \<sigma>\<close> have "(THE v. index \<sigma> v = t) = v"
    by (auto simp: index_less_size_conv)

  with assms filter_eq v have "\<sigma> = \<sigma>'[v \<mapsto> t]"
    by (metis distinct_count_in_set index_less_size_conv move_to_def move_to_id permutations_of_setD(2))

  have "\<And>v'. \<sigma> = \<sigma>'[v' \<mapsto> t] \<Longrightarrow> v' = v"
    apply (rule move_to_eq_unique_vertex[symmetric, OF assms(3) assms(1) \<open>index \<sigma> v = t\<close>])
     apply (metis \<open>index \<sigma> v = t\<close> assms(1) assms(2) index_less_size_conv permutations_of_setD(1))
    by blast

  with v \<open>\<sigma> = \<sigma>'[v \<mapsto> t]\<close> have "{v. \<sigma> = \<sigma>'[v \<mapsto> t]} = {v}"
    by blast
    
  with v show "card (V \<inter> {v. \<sigma> = \<sigma>'[v \<mapsto> t]}) = 1"
    by simp
qed

lemma permutation_vertex_at_tE:
  assumes "\<sigma> \<in> permutations_of_set V" "v \<in> V" "t < length \<sigma>"
  obtains \<sigma>' where "\<sigma>' \<in> permutations_of_set V" "index \<sigma>' v = t" "[x <- \<sigma>'. x \<noteq> v] = [x <- \<sigma>. x \<noteq> v]"
proof
  from assms show perm: "\<sigma>[v \<mapsto> t] \<in> permutations_of_set V"
    by (auto intro!: permutations_of_setI dest: permutations_of_setD simp: move_to_set_eq move_to_distinct)

  from assms show "index \<sigma>[v \<mapsto> t] v = t"
    by (auto intro: move_to_index_v distinct_filter dest: permutations_of_setD)

  from assms perm show "[x <- \<sigma>[v \<mapsto> t]. x \<noteq> v] = [x <- \<sigma>. x \<noteq> v]"
    by (smt (verit, ccfv_threshold) distinct_move_to_indices_if_eq distinct_order_filter_eq filter_cong permutations_of_setD(1) permutations_of_setD(2))
qed

lemma permutations_but_v_bij_betw:
  assumes "\<sigma> \<in> permutations_of_set V"
  assumes "index \<sigma> v = t" "v \<in> V"
  shows "bij_betw (\<lambda>\<sigma>'. index \<sigma>' v) {\<sigma>' \<in> permutations_of_set V. [x <- \<sigma>'. x \<noteq> v] = [x <- \<sigma>. x \<noteq> v]} {..<length \<sigma>}" (is "bij_betw ?f ?L ?R")
  unfolding bij_betw_def
proof
  show "inj_on ?f ?L"
    apply (auto intro!: inj_onI)
    apply (smt (verit, del_insts) assms(3) distinct_count_in_set filter_cong mem_Collect_eq move_to_def move_to_id permutations_of_setD(1) permutations_of_setD(2))
    done
next
  from assms show "?f ` ?L = ?R"
    apply (auto)
     apply (metis index_less_size_conv length_finite_permutations_of_set permutations_of_setD(1))
  proof -
    fix x
    assume "x < length \<sigma>"
    with assms obtain \<sigma>' where "\<sigma>' \<in> permutations_of_set V" "index \<sigma>' v = x" "[x <- \<sigma>'. x \<noteq> v] = [x <- \<sigma>. x \<noteq> v]"
      by (auto elim: permutation_vertex_at_tE)

    then show "x \<in> (\<lambda>\<sigma>'. index \<sigma>' v) ` {\<sigma>' \<in> permutations_of_set V. filter (\<lambda>x. x \<noteq> v) \<sigma>' = filter (\<lambda>x. x \<noteq> v) \<sigma>}"
      by blast
  qed
qed

lemma permutations_but_v_card:
  assumes "\<sigma> \<in> permutations_of_set V"
  assumes "index \<sigma> v = t" "v \<in> V"
  shows "card {\<sigma>' \<in> permutations_of_set V. [x <- \<sigma>'. x \<noteq> v] = [x <- \<sigma>. x \<noteq> v]} = card V"
  using assms
  apply (auto dest!: permutations_but_v_bij_betw bij_betw_same_card)
  using assms(1) length_finite_permutations_of_set by blast

lemma card_singleton_UN:
  assumes "\<forall>x \<in> X. \<exists>y. x = {y}"
  shows "card (\<Union> X) = card X"
  using assms
  by (auto intro!: bij_betw_same_card[of "\<lambda>x. {x}"] intro!: bij_betwI[where g = "\<lambda>X. (THE x. X = {x})"])

lemma matched_indices_set_eq:
  assumes "bipartite M U (set xs)"
  assumes "distinct xs"
  assumes "matching M"
  shows "{..<length xs} \<inter> {t. xs ! t \<in> Vs M} = (index xs) ` \<Union> (((\<inter>) (set xs)) ` M)"
  using assms
  by (auto elim: distinct_indexE intro!: rev_image_eqI simp: Vs_def)

lemma expectation_sum_pmf_of_set:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> real"
  assumes "S \<noteq> {}" "finite S"
  shows "measure_pmf.expectation (pmf_of_set S) (\<lambda>e. \<Sum>x\<in>A. f x e) =
    (\<Sum>x\<in>A. measure_pmf.expectation (pmf_of_set S) (\<lambda>e. f x e))"
  using assms
  by (simp add: integral_pmf_of_set flip: sum_divide_distrib, subst sum.swap) blast

lemma bool_pmf_is_bernoulli_pmf:
  "\<exists>p. bool_pmf = bernoulli_pmf p \<and> 0 \<le> p \<and> p \<le> 1"
  apply (auto simp: pmf_eq_iff)
  by (metis (full_types) pmf_False_conv_True pmf_bernoulli_True pmf_le_1 pmf_nonneg)

lemma bool_pmf_is_bernoulli_pmfE:
  obtains p where "bool_pmf = bernoulli_pmf p" "0 \<le> p" "p \<le> 1"
  using bool_pmf_is_bernoulli_pmf
  by blast

lemma bernoulli_prob_True_expectation:
  "measure_pmf.prob p {True} = measure_pmf.expectation p of_bool"
proof -
  obtain p' where p': "p = bernoulli_pmf p'" "0 \<le> p'" "p' \<le> 1"
    using bool_pmf_is_bernoulli_pmfE by blast

  then show ?thesis
    by (auto simp: measure_pmf_single)
qed

lemma indicator_singleton: "indicator {x} y = (if  x = y then 1 else 0)"
  by (auto simp add: indicator_eq_1_iff)

lemma sum_eq_card_where_One:
  assumes "finite A"
  assumes "card {x \<in> A. f x = 1} = n"
  assumes "\<forall>x. f x \<noteq> 0 \<longrightarrow> f x = 1"
  shows "sum f A = real n"
proof -
  have "sum f A = sum f ({a \<in> A. f a = 0} \<union> {a \<in> A. f a \<noteq> 0})"
    by (auto intro: sum.cong)

  also have "\<dots> = sum f {a \<in> A. f a = 0} + sum f {a \<in> A. f a \<noteq> 0}"
    by (rule sum.union_disjoint)
       (use \<open>finite A\<close> in auto)

  also have "\<dots> = sum f {a \<in> A. f a \<noteq> 0}"
    by (auto intro: sum.neutral)

  also have "\<dots> = sum f {a \<in> A. f a = 1}"
    using \<open>\<forall>x. f x \<noteq> 0 \<longrightarrow> f x = 1\<close>
    by (metis zero_neq_one)

  also have "\<dots> = n"
    using assms
    by simp

  finally show ?thesis .
qed

lemma infsetsum_sum_cong:
  assumes "finite {a \<in> A. f a \<noteq> 0}"
  assumes "finite B"
  assumes "\<And>a. a \<in> B - A \<Longrightarrow> f a = 0"
  assumes "\<And>a. a \<in> B - A \<Longrightarrow> g a = 0"
  assumes "\<And>a. a \<in> A \<Longrightarrow> f a \<noteq> 0 \<Longrightarrow> a \<in> B"
  assumes "\<And>a. a \<in> A \<Longrightarrow> a \<in> B \<Longrightarrow> f a = g a"
  shows "infsetsum f A = sum g B"
proof -
  have "infsetsum f A = infsetsum g B"
    using assms
    by (intro infsetsum_cong_neutral) blast+

  also have "\<dots> = sum g B"
    using assms
    by simp

  finally show ?thesis .
qed

lemma pmf_of_perms_finite_support:
  assumes "finite V"
  shows  "finite (set_pmf (pmf_of_set (permutations_of_set V)))"
  using assms
  by simp

lemma bool_pmf_imp_prob_leq:
  assumes finite_support: "finite (set_pmf p)"
  assumes imp: "\<forall>\<sigma> \<in> set_pmf p. P \<sigma> \<longrightarrow> Q \<sigma>"
  shows "measure_pmf.prob (do {\<sigma> \<leftarrow> p; return_pmf (P \<sigma>)}) {True} \<le> measure_pmf.prob (do {\<sigma> \<leftarrow> p; return_pmf (Q \<sigma>)}) {True}"
proof -
  have "infsetsum (\<lambda>x. pmf p x * (if P x then 1 else 0)) UNIV = infsetsum (\<lambda>x. pmf p x * (if P x then 1 else 0)) (set_pmf p)"
    by (auto simp: set_pmf_iff intro: infsetsum_cong_neutral)

  also have "\<dots> = sum (\<lambda>x. pmf p x * (if P x then 1 else 0)) (set_pmf p)"
    using finite_support by simp

  also have "\<dots> \<le> sum (\<lambda>x. pmf p x * (if Q x then 1 else 0)) (set_pmf p)"
    using imp
    by (simp add: sum_mono)

  also have "\<dots> = infsetsum (\<lambda>x. pmf p x * (if Q x then 1 else 0)) (set_pmf p)"
    using finite_support by simp

  also have "\<dots> = infsetsum (\<lambda>x. pmf p x * (if Q x then 1 else 0)) UNIV"
    by (auto simp: set_pmf_iff intro: infsetsum_cong_neutral)

  finally have "infsetsum (\<lambda>x. pmf p x * (if P x then 1 else 0)) UNIV \<le> infsetsum (\<lambda>x. pmf p x * (if Q x then 1 else 0)) UNIV" .

  then show ?thesis
    by (auto simp: pmf_bind measure_pmf_conv_infsetsum pmf_expectation_eq_infsetsum indicator_singleton)
qed

lemma bind_bind_pair_pmf:
  includes monad_normalisation
  shows
  "do {
    x \<leftarrow> p1;
    y \<leftarrow> p2;
    return_pmf (f x y)
   }
   =
   do {
    (x,y) \<leftarrow> pair_pmf p1 p2;
    return_pmf (f x y)
   }"
  by (simp add: pair_pmf_def)

lemma bool_pmf_imp_prob_leq2:
  assumes finite_support: "finite (set_pmf p1)" "finite (set_pmf p2)"
  assumes imp: "\<forall>x\<in>set_pmf p1. \<forall>y\<in>set_pmf p2. P x y \<longrightarrow> Q x y"
  shows "measure_pmf.prob (do {x \<leftarrow> p1; y \<leftarrow> p2; return_pmf (P x y)}) {True} \<le>
    measure_pmf.prob (do {x \<leftarrow> p1; y \<leftarrow> p2; return_pmf (Q x y)}) {True}" (is "?L \<le> ?R")
proof -
  have "?L =
    measure_pmf.prob (do {xy \<leftarrow> pair_pmf p1 p2; return_pmf (P (fst xy) (snd xy))}) {True}"
    by (simp add: bind_bind_pair_pmf case_prod_beta')

  also have "\<dots> \<le> measure_pmf.prob (do {xy \<leftarrow> pair_pmf p1 p2; return_pmf (Q (fst xy) (snd xy))}) {True}"
    using assms
    by (auto intro!: bool_pmf_imp_prob_leq)

  also have "\<dots> = ?R"
    by (simp add: bind_bind_pair_pmf case_prod_beta')

  finally show "?L \<le> ?R" .
qed

lemma card_perms_components:
  assumes "finite V" "X \<subseteq> V"
  shows "card {(xs, vs). xs \<subseteq> {0..<card V} \<and> card xs = card X \<and> vs \<in> permutations_of_set (V - X)} = (card V choose card X) * fact (card V - card X)" (is "card ?L = ?R")
proof -
  have "?L = {xs. xs \<subseteq> {0..<card V} \<and> card xs = card X} \<times> permutations_of_set (V-X)"
    by blast

  with assms show ?thesis
    by (auto simp: card_Diff_subset[OF finite_subset] n_subsets)
qed
(* 
fun rebuild :: "nat list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rebuild [] acc [] = acc"
| "rebuild (n#ns) acc (v#\<sigma>') = rebuild ns (take n acc @ v # drop n acc) \<sigma>'"
| "rebuild ns acc \<sigma>' = []"
 *)
fun decr :: "nat \<Rightarrow> nat" where
  "decr 0 = 0"
| "decr (Suc n) = n"

lemma decr_leq: "decr n \<le> n"
  by (cases n) auto

lemma decr_le: "n \<noteq> 0 \<Longrightarrow> decr n < n"
  by (cases n) auto

lemma decr_mono: "n \<le> b \<Longrightarrow> decr n \<le> b"
  using decr_leq dual_order.trans by blast

lemma decr_strict_mono: "n < b \<Longrightarrow> decr n < b"
  using decr_leq order_le_less_trans by auto

lemma decr_Suc: "x \<noteq> 0 \<Longrightarrow> Suc (decr x) = x"
  by (cases x) auto

lemma decr_bij_betw: "\<forall>x \<in> X. x \<noteq> 0 \<Longrightarrow> bij_betw decr X (decr ` X)"
  by (rule bij_betwI[where g = Suc]) (auto simp: decr_Suc)

fun rebuild :: "nat list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rebuild [] [] xs = xs"
| "rebuild (0#ns) (v#\<sigma>') xs = v # rebuild (map decr ns) \<sigma>' xs"
| "rebuild (Suc n#ns) \<sigma>' (x#xs) = x # rebuild (map decr (Suc n#ns)) \<sigma>' xs"
| "rebuild ns \<sigma>' xs = \<sigma>' @ xs"

lemma set_take_insert_drop: "set ((take n xs) @ x # (drop n xs)) = {x} \<union> set xs"
  by (induction xs n rule: induct_list_nat)
     (simp_all add: insert_commute)

lemma set_rebuild_subset:
  shows "set (rebuild ns \<sigma>' xs) \<subseteq> set xs \<union> set \<sigma>'"
  by (induction ns \<sigma>' xs rule: rebuild.induct) auto

lemma set_rebuild_subset':
  "v \<in> set (rebuild ns \<sigma>' xs) \<Longrightarrow> v \<in> set xs \<union> set \<sigma>'"
  using set_rebuild_subset by fast

lemma distinct_rebuild:
  assumes "set xs \<inter> set \<sigma>' = {}"
  assumes "distinct \<sigma>'"
  assumes "distinct xs"
  shows "distinct (rebuild ns xs \<sigma>')"
  using assms set_rebuild_subset
  by (induction ns xs \<sigma>' rule: rebuild.induct) force+

lemma decr_gt_if: "0 < n \<Longrightarrow> n < Suc k \<Longrightarrow> decr n < k"
  by (cases n) auto

lemma map_decr_gt: "\<forall>n \<in> set ns. 0 < n \<and> n < Suc k \<Longrightarrow> \<forall>n \<in> set (map decr ns). n < k"
  by (induction ns) (auto dest: decr_gt_if)

lemma map_decr_sorted_wrt: "\<forall>n \<in> set ns. 0 < n \<Longrightarrow> sorted_wrt (<) ns \<Longrightarrow> sorted_wrt (<) (map decr ns)"
  using gr0_conv_Suc
  by (induction ns) fastforce+

lemma set_rebuild:
  assumes "length ns = length \<sigma>'"
  assumes "\<forall>n \<in> set ns. n < length \<sigma>' + length xs"
  assumes "sorted_wrt (<) ns"
  shows "set (rebuild ns \<sigma>' xs) = set xs \<union> set \<sigma>'"
  using assms
proof (induction ns \<sigma>' xs rule: rebuild.induct)
  case (2 ns v \<sigma>' xs)
  then have "\<forall>n\<in>set (map decr ns). n < length \<sigma>' + length xs"
    by (intro map_decr_gt) simp

  with 2 have "set (rebuild (map decr ns) \<sigma>' xs) = set xs \<union> set \<sigma>'"
    by (auto intro: "2.IH" map_decr_sorted_wrt)

  then show ?case
    by simp
next
  case (3 n ns \<sigma>' x xs)
  then have "\<forall>n\<in>set (map decr (Suc n # ns)). n < length \<sigma>' + length xs"
    by (intro map_decr_gt) auto

  with 3 have "set (rebuild (map decr (Suc n # ns)) \<sigma>' xs) = set xs \<union> set \<sigma>'"
  proof (intro "3.IH", goal_cases)
    case 3
    then show ?case
      by (intro map_decr_sorted_wrt) auto
  qed simp

  then show ?case
    by simp
qed auto

lemma set_rebuild_cong:
  assumes "length ns = length \<sigma>'"
  assumes "\<forall>n \<in> set ns. n < length \<sigma>' + length xs"
  assumes "sorted_wrt (<) ns"
  assumes "set xs \<union> set \<sigma>' = V"
  shows "set (rebuild ns \<sigma>' xs) = V"
  using assms
  by (auto dest: set_rebuild)

lemma rebuild_filter_left:
  assumes "sorted_wrt (<) ns"
  assumes "length ns = length \<sigma>'"
  assumes "\<forall>n \<in> set ns. n < length \<sigma>' + length xs"
  assumes "set xs \<inter> X = {}"
  assumes "set \<sigma>' \<subseteq> X"
  \<comment> \<open>The following two assumptions are not strictly necessary but make the proof easier.\<close>
  assumes "distinct \<sigma>'"
  assumes "distinct xs"
  shows "[v <- rebuild ns \<sigma>' xs. v \<in> X] = \<sigma>'"
  using assms
proof (intro distinct_same_order_list_eq, goal_cases)
  case 1
  then show ?case
    by (auto intro!: distinct_filter intro: distinct_rebuild)
next
  case 2
  then show ?case
    by blast
next
  case 3
  then show ?case
    by (simp only: filter_set[symmetric] set_rebuild) auto
next
  case 4
  then show ?case
  proof (induction ns \<sigma>' xs rule: rebuild.induct)
    case (1 xs)
    then have "filter (\<lambda>v. v \<in> X) (rebuild [] [] xs) = []"
      by (auto intro: filter_False)
    then show ?case
      by simp
  next
    case (2 ns v \<sigma>' xs)

    have IH: "\<forall>x y. (index (filter (\<lambda>v. v \<in> X) (rebuild (map decr ns) \<sigma>' xs)) x \<le> index (filter (\<lambda>v. v \<in> X) (rebuild (map decr ns) \<sigma>' xs)) y) = (index \<sigma>' x \<le> index \<sigma>' y)"
    proof (intro "2.IH", goal_cases)
      case 1
      from \<open>sorted_wrt (<) (0 # ns)\<close> show ?case
        by (auto intro: map_decr_sorted_wrt)
    next
      case 3
      from \<open>\<forall>n\<in>set (0 # ns). n < length (v # \<sigma>') + length xs\<close> \<open>sorted_wrt (<) (0 # ns)\<close>
      show ?case
        by (intro map_decr_gt) simp
    qed (use "2.prems" in auto)

    from \<open>set (v # \<sigma>') \<subseteq> X\<close> have filter_cons: "filter (\<lambda>v. v \<in> X) (rebuild (0 # ns) (v # \<sigma>') xs) = v # filter (\<lambda>v. v \<in> X) (rebuild (map decr ns) \<sigma>' xs)"
      by simp

    show ?case
      by (simp only: filter_cons) (auto simp: IH)
  next
    case (3 n ns \<sigma>' x xs)

    have IH: "\<forall>x y. (index (filter (\<lambda>v. v \<in> X) (rebuild (map decr (Suc n # ns)) \<sigma>' xs)) x \<le> index (filter (\<lambda>v. v \<in> X) (rebuild (map decr (Suc n # ns)) \<sigma>' xs)) y) = (index \<sigma>' x \<le> index \<sigma>' y)"
    proof (intro "3.IH", goal_cases)
      case 1
      from \<open>sorted_wrt (<) (Suc n # ns)\<close> show ?case
        by (intro map_decr_sorted_wrt) fastforce+
    next
      case 3
      from \<open>\<forall>n\<in>set (Suc n # ns). n < length \<sigma>' + length (x # xs)\<close> \<open>sorted_wrt (<) (Suc n # ns)\<close>
      show ?case
        by (intro map_decr_gt) fastforce
    qed (use "3.prems" in auto)

    from \<open>set (x # xs) \<inter> X = {}\<close> have filter_cons:"filter (\<lambda>v. v \<in> X) (rebuild (Suc n # ns) \<sigma>' (x # xs)) = filter (\<lambda>v. v \<in> X) (rebuild (map decr (Suc n # ns)) \<sigma>' xs)"
      by simp

    with IH show ?case
      by force
  next
    case ("4_1" n ns \<sigma>')
    then have "filter (\<lambda>v. v \<in> X) (rebuild (Suc n # ns) \<sigma>' []) = \<sigma>'"
      by (auto intro: filter_True)
    then show ?case
      by simp
  next
    case ("4_4" v \<sigma>' xs)
    then have "filter (\<lambda>v. v \<in> X) (rebuild [] (v # \<sigma>') xs) = v # \<sigma>'"
      by (auto intro: filter_True)
    then show ?case
      by simp
  next
    case ("4_5" n ns v \<sigma>')
    then have "filter (\<lambda>v. v \<in> X) (rebuild (Suc n # ns) (v # \<sigma>') []) = v # \<sigma>'"
      by (auto intro: filter_True)
    then show ?case
      by simp
  qed auto
qed

lemma rebuild_filter_right:
  assumes "set \<sigma>' \<subseteq> X"
  assumes "set xs \<inter> X = {}"
  shows "[v <- rebuild ns \<sigma>' xs. v \<notin> X] = xs"
  using assms
  by (induction ns \<sigma>' xs rule: rebuild.induct)
     (auto intro: filter_True filter_False simp add: disjoint_iff subsetD)

lemma filter_permutation_subset: "\<sigma> \<in> permutations_of_set V \<Longrightarrow> X \<subseteq> V \<Longrightarrow> [v <- \<sigma>. v \<in> X] \<in> permutations_of_set X"
  by (rule permutations_of_setI) (auto dest: permutations_of_setD)

lemma filter_permutation_subset_cong: "\<sigma> \<in> permutations_of_set V \<Longrightarrow> X \<subseteq> V \<Longrightarrow> \<sigma>' = [v <- \<sigma>. v \<in> X] \<Longrightarrow> \<sigma>' \<in> permutations_of_set X"
  by (auto intro: filter_permutation_subset)

lemma decr_index_index_tl: "hd \<sigma> \<notin> set \<sigma>' \<Longrightarrow> x \<in> set \<sigma>' \<Longrightarrow> decr (index \<sigma> x) = index (tl \<sigma>) x"
  by (induction \<sigma>) (auto)

lemma map_index_tl_map_decr_0:
  assumes "distinct (v#\<sigma>s)"
  assumes "subseq (v'#\<sigma>'s) (v#\<sigma>s)"
  assumes "map (index \<sigma>) (v'#\<sigma>'s) = (0::nat) # ns"
  assumes "\<sigma> = v # \<sigma>s"
  shows "map decr ns = map (index \<sigma>s) \<sigma>'s"
  using assms
  apply (auto split: if_splits)
  by (meson subseq_order.dual_order.trans subseq_singleton_left)

lemma map_index_tl_map_decr_Suc:
  assumes "distinct \<sigma>"
  assumes "subseq \<sigma>' \<sigma>"
  assumes "Suc n # ns = map (index \<sigma>) \<sigma>'"
  shows "map decr (Suc n # ns) = map (index (tl \<sigma>)) \<sigma>'"
  using assms
  apply (induction \<sigma>)
   apply (auto split: if_splits)
  by (meson subseq_Cons' subseq_order.dual_order.trans subseq_singleton_left)

lemma map_decr_map_index_map_index_tl:
  assumes "hd \<sigma> \<notin> set \<sigma>'"
  shows "map decr (map (index \<sigma>) \<sigma>') = map (index (tl \<sigma>)) \<sigma>'"
  using assms
  by (auto simp: decr_index_index_tl)

lemma list_emb_drop_before_first:
  assumes "list_emb P xs (ys@zs)"
  assumes "\<forall>y \<in> set ys. \<not>P (hd xs) y"
  shows "list_emb P xs zs"
  using assms
  apply (induction ys)
   apply simp_all
  by (metis list.exhaust_sel list_emb_Cons_iff2 list_emb_Nil)

lemma sorted_list_of_set_is_map_index:
  assumes "distinct \<sigma>"
  assumes "subseq \<sigma>' \<sigma>"
  assumes "\<sigma>' \<in> permutations_of_set X"
  shows "sorted_list_of_set (index \<sigma> ` X) = map (index \<sigma>) \<sigma>'"
proof -
  consider (inf) "infinite X" | (empty) "X = {}" | (fin_nonempty) "finite X \<and> X \<noteq> {}" by blast
  then show ?thesis
  proof cases
    case inf
    with assms have False
      by (auto dest: permutations_of_set_infinite)
    then show ?thesis by blast
  next
    case empty
    with assms show ?thesis
      by simp
  next
    case fin_nonempty
    with assms show ?thesis
    proof (induction \<sigma>' arbitrary: X)
      case Nil
      then show ?case
        by (auto dest: permutations_of_setD)
    next
      case (Cons v \<sigma>')

      consider (single) "X - {v} = {}" | (ind) "X - {v} \<noteq> {}" by blast
      then show ?case
      proof cases
        case single
        with Cons.prems have "X = {v}" by blast
        with Cons.prems have "\<sigma>' = []"
          by (auto dest: permutations_of_setD)

        with \<open>X = {v}\<close> show ?thesis
          by simp
      next
        case ind

        with Cons.prems have fin': "finite' (X - {v})"
          by blast

        from Cons.prems have "subseq \<sigma>' \<sigma>"
          by (auto intro: subseq_Cons')
      
        have perm: "\<sigma>' \<in> permutations_of_set (X - {v})"
        proof (intro permutations_of_setI equalityI subsetI DiffI, goal_cases)
          case (1 x)
          with Cons show ?case
            by (auto dest: permutations_of_setD)
        next
          case (2 x)
          with Cons show ?case
            by (auto dest: permutations_of_setD)
        next
          case (3 x)
          with Cons show ?case
            by (auto dest: permutations_of_setD)
        next
          case 4
          with Cons show ?case
            by (auto dest: permutations_of_setD)
        qed
  
        from Cons.prems have sorted_Cons: "sorted_list_of_set (index \<sigma> ` X) = index \<sigma> v # sorted_list_of_set ((index \<sigma>) ` (X - {v}))"
        proof (intro sorted_list_of_set_image_Cons, goal_cases)
          case 3
          show ?case
          proof (rule ccontr, simp)
            assume "\<exists>x\<in>X. \<not> index \<sigma> v \<le> index \<sigma> x"

            then obtain x where x: "x \<in> X" "index \<sigma> x < index \<sigma> v"
              by force

            then have v_not_in_take: "v \<notin> set (take (Suc (index \<sigma> x)) \<sigma>)"
              by (simp add: index_take)

            have "subseq (v#\<sigma>') (drop (Suc (index \<sigma> x)) \<sigma>)"
            proof (rule list_emb_drop_before_first[where ys = "take (Suc (index \<sigma> x)) \<sigma>"], goal_cases)
              case 1
              from \<open>subseq (v#\<sigma>') \<sigma>\<close> show ?case
                by simp
            next
              case 2
              from v_not_in_take show ?case
                by auto
            qed

            with x \<open>v#\<sigma>' \<in> permutations_of_set X\<close> have after_v: "x \<in> set (drop (Suc (index \<sigma> x)) \<sigma>)"
              by (metis permutations_of_setD(1) subseq_order.dual_order.trans subseq_singleton_left)

            from x \<open>distinct \<sigma>\<close> have "x \<notin> set (drop (Suc (index \<sigma> x)) \<sigma>)"
              by (intro set_drop_if_index) blast+

            with after_v show False
              by blast
          qed
        next
          case 5
          then show ?case
            by (auto dest: permutations_of_setD elim!: list_emb_set intro!: inj_on_index2)
        qed (use Cons in \<open>auto dest: permutations_of_setD\<close>)

        with Cons.IH[OF \<open>distinct \<sigma>\<close> \<open>subseq \<sigma>' \<sigma>\<close> perm fin'] Cons.prems show ?thesis
          by (simp add: sorted_Cons)
      qed
    qed
  qed
qed

lemma rebuild_rebuilds:
  assumes "finite V"
  assumes "X \<subseteq> V"
  assumes "\<sigma> \<in> permutations_of_set V"
  assumes "\<sigma>' = filter (\<lambda>v. v \<in> X) \<sigma>"
  assumes "xs = filter (\<lambda>v. v \<notin> X) \<sigma>"
  shows "rebuild (map (index \<sigma>) \<sigma>') \<sigma>' xs = \<sigma>"
  using assms
proof (induction "map (index \<sigma>) \<sigma>'" \<sigma>' xs arbitrary: \<sigma> X V rule: rebuild.induct)
  case (1 xs)
  then show ?case
    by (metis filter_True filter_empty_conv rebuild.simps(1))
next
  case (2 ns v' \<sigma>' xs)

  then have perm': "v' # \<sigma>' \<in> permutations_of_set X"
    by (auto intro: filter_permutation_subset_cong)

  from 2 have v'_hd: "index \<sigma> v' = 0"
    by force

  then have \<sigma>_tl: "\<sigma> = v' # tl \<sigma>"
    by (metis "2.prems"(4) Nitpick.size_list_simp(2) filter.simps(1) index_Cons index_eq_index_conv list.collapse list.distinct(1) nat.simps(3) size_index_conv)

  then have \<sigma>_nonempty: "\<sigma> \<noteq> []" by blast

  from 2 \<sigma>_tl have map_decr_ns_map_index_tl: "map decr ns = map (index (tl \<sigma>)) \<sigma>'"
  proof (intro map_index_tl_map_decr_0[where v=v' and v'=v' and \<sigma>=\<sigma>], goal_cases)
    case 1
    then show ?case
      by (auto dest: permutations_of_setD)
  next
    case 2
    then show ?case
      by (metis subseq_filter_left)
  next
    case 3
    then show ?case
      by argo
  next
    case 4
    then show ?case
      by blast
  qed

  have rebuild_tl: "rebuild (map (index (tl \<sigma>)) \<sigma>') \<sigma>' xs = tl \<sigma>"
  proof (rule "2.hyps"(1)[OF map_decr_ns_map_index_tl, where V = "V - {v'}" and X = "X - {v'}"], goal_cases)
    case 1
    from \<open>finite V\<close> show ?case by blast
  next
    case 2
    from \<open>X \<subseteq> V\<close> show ?case by blast
  next
    case 3
    then show ?case
    proof (intro permutations_of_setI equalityI subsetI DiffI, goal_cases)
      case (1 x)
      with \<open>\<sigma> \<in> permutations_of_set V\<close> \<sigma>_nonempty show ?case
        by (auto dest: list.set_sel permutations_of_setD)
    next
      case (2 x)
      with \<open>\<sigma> \<in> permutations_of_set V\<close> show ?case
        by (metis \<sigma>_tl distinct.simps(2) permutations_of_setD(2) singletonD)
    next
      case (3 x)
      with \<open>\<sigma> \<in> permutations_of_set V\<close> \<sigma>_tl show ?case
        by (metis Diff_iff insertI1 permutations_of_setD(1) set_ConsD)
    next
      case 4
      with \<open>\<sigma> \<in> permutations_of_set V\<close> show ?case
        by (auto dest: distinct_tl permutations_of_setD)
    qed
  next
    case 4
    from perm' show ?case
      by (intro filter_tl_without_hd)
         (auto dest: permutations_of_setD intro: \<open>v' # \<sigma>' = filter (\<lambda>v. v \<in> X) \<sigma>\<close>)
  next
    case 5
    from \<open>xs = filter (\<lambda>v. v \<notin> X) \<sigma>\<close> show ?case
      apply (auto intro:)   
      by (smt (verit, best) "2.prems"(3) \<sigma>_tl distinct.simps(2) filter.simps(2) filter_cong list.set_intros(1) perm' permutations_of_setD(1) permutations_of_setD(2))
  qed

  note map_map[simp del]
  from \<open>v' # \<sigma>' \<in> permutations_of_set X\<close> have "hd \<sigma> \<notin> set \<sigma>'"
    by (subst \<open>\<sigma> = v' # tl \<sigma>\<close>) (auto dest!: permutations_of_setD)

  then show ?case
    by (simp add: v'_hd map_decr_map_index_map_index_tl rebuild_tl, subst (2) \<sigma>_tl) blast
next
  case (3 n ns \<sigma>' x xs)

  then have "x \<notin> X"
    by (metis (no_types, lifting) list.set_intros(1) mem_Collect_eq set_filter)

  from 3 have \<sigma>_tl: "\<sigma> = x # tl \<sigma>"
    by (smt (verit, ccfv_SIG) Cons_eq_map_D filter.simps(1) filter.simps(2) index_Cons list.collapse list.inject nat.simps(3))

  then have \<sigma>_nonempty: "\<sigma> \<noteq> []" by blast

  have map_decr_nns_map_index_tl: "map decr (Suc n # ns) = map (index (tl \<sigma>)) \<sigma>'"
  proof (intro map_index_tl_map_decr_Suc, goal_cases)
    case 1
    from \<open>\<sigma> \<in> permutations_of_set V\<close> show ?case
      by (auto dest: permutations_of_setD)
  next
    case 2
    from \<open>\<sigma>' = filter (\<lambda>v. v \<in> X) \<sigma>\<close> subseq_filter_left show ?case
      by blast
  next
    case 3
    from \<open>Suc n # ns = map (index \<sigma>) \<sigma>'\<close> show ?case by blast
  qed

  have rebuild_tl: "rebuild (map (index (tl \<sigma>)) \<sigma>') \<sigma>' xs = tl \<sigma>"
  proof (rule "3.hyps"(1)[OF map_decr_nns_map_index_tl, where V = "V - {x}" and X = X], goal_cases)
    case 1
    from \<open>finite V\<close> show ?case by blast
  next
    case 2
    from \<open>X \<subseteq> V\<close> \<open>x \<notin> X\<close> show ?case by blast
  next
    case 3
    show ?case
    proof (intro permutations_of_setI equalityI subsetI DiffI, goal_cases)
      case (1 y)
      with \<sigma>_nonempty \<open>\<sigma> \<in> permutations_of_set V\<close> show ?case
        by (auto dest: permutations_of_setD list.set_sel)
    next
      case (2 y)
      with \<sigma>_tl \<open>\<sigma> \<in> permutations_of_set V\<close> show ?case
        by (metis distinct.simps(2) permutations_of_setD(2) singletonD)
    next
      case (3 y)
      with \<sigma>_tl \<open>\<sigma> \<in> permutations_of_set V\<close> show ?case
        by (metis DiffD1 DiffD2 insertI1 permutations_of_setD(1) set_ConsD)
    next
      case 4
      from \<open>\<sigma> \<in> permutations_of_set V\<close> show ?case
        by (auto dest: permutations_of_setD distinct_tl)
    qed
  next
    case 4
    from \<sigma>_tl \<open>x \<notin> X\<close> \<open>\<sigma>' = filter (\<lambda>v. v \<in> X) \<sigma>\<close> show ?case
      by (metis filter.simps(2))
  next
    case 5
    from \<sigma>_tl \<open>x \<notin> X\<close> \<open>x # xs = filter (\<lambda>v. v \<notin> X) \<sigma>\<close> show ?case
      by (metis filter.simps(2) list.inject)
  qed

  note list.map[simp del]
  show ?case
    by (simp flip: \<open>Suc n # ns = map (index \<sigma>) \<sigma>'\<close> add: map_decr_nns_map_index_tl, subst \<sigma>_tl, simp add:  rebuild_tl)
next
  case ("4_1" n ns \<sigma>')
  then show ?case
    by (metis append.right_neutral filter_True filter_empty_conv rebuild.simps(4))
next
  case ("4_2" ns xs)
  then show ?case
    by blast
next
  case ("4_3" n ns)
  then show ?case
    by blast
next
  case ("4_4" v \<sigma>' xs)
  then show ?case
    by blast
next
  case ("4_5" n ns v \<sigma>')
  then show ?case
    by (metis append.right_neutral filter_True filter_empty_conv rebuild.simps(4))
qed

lemma sorted_strict_last_geq_length_offset:
  assumes "ns \<noteq> []"
  assumes "sorted_wrt (<) ns"
  assumes "h < hd ns"
  shows "length ns + h \<le> last ns"
  using assms
proof (induction ns arbitrary: h)
  case (Cons n ns)
  note cons' = Cons
  show ?case
  proof (cases ns)
    case Nil
    with Cons show ?thesis
      by simp
  next
    case (Cons n' ns')
    with cons' have "Suc h < hd ns" by simp

    with cons' show ?thesis
      by fastforce
  qed
qed simp

lemma sorted_strict_last_geq_length:
  assumes "ns \<noteq> []"
  assumes "sorted_wrt (<) ns"
  assumes "0 < hd ns"
  shows "length ns \<le> last ns"
  using assms
  by (auto dest: sorted_strict_last_geq_length_offset)

lemma rebuild_indices:
  assumes "sorted_wrt (<) ns"
  assumes "length ns = length \<sigma>'"
  assumes "\<forall>n \<in> set ns. n < length \<sigma>' + length xs"
  assumes "set xs \<inter> X = {}"
  assumes "set \<sigma>' = X"
  assumes "distinct \<sigma>'"
  shows "index (rebuild ns \<sigma>' xs) ` X = set ns"
  using assms
proof (induction ns \<sigma>' xs arbitrary: X rule: rebuild.induct)
  case (1 xs)
  then show ?case
    by simp
next
  case (2 ns v \<sigma>' xs)

  have IH: "index (rebuild (map decr ns) \<sigma>' xs) ` (X - {v}) = set (map decr ns)"
  proof (intro "2.IH", goal_cases)
    case 1
    from \<open>sorted_wrt (<) (0#ns)\<close> show ?case
      by (auto intro: map_decr_sorted_wrt)
  next
    case 2
    from \<open>length (0#ns) = length (v#\<sigma>')\<close> show ?case by simp
  next
    case 3
    from \<open>\<forall>n \<in> set (0#ns). n < length (v#\<sigma>') + length xs\<close> \<open>sorted_wrt (<) (0 # ns)\<close> show ?case
      by (intro map_decr_gt) auto
  next
    case 4
    from \<open>set xs \<inter> X = {}\<close> show ?case by blast
  next
    case 5
    from \<open>set (v#\<sigma>') = X\<close> \<open>distinct (v#\<sigma>')\<close> show ?case by force
  next
    case 6
    from \<open>distinct (v#\<sigma>')\<close> show ?case by simp
  qed

  from \<open>set (v#\<sigma>') = X\<close> have X_In_v: "X \<inter> {v} = {v}" by fastforce

  have "index (rebuild (0 # ns) (v # \<sigma>') xs) ` X = insert 0 (Suc ` (index (rebuild (map decr ns) \<sigma>' xs) ` (X - {v})))"
    by (auto simp add: X_In_v)

  also have "\<dots> = insert 0 (Suc ` set (map decr ns))"
    by (simp add: IH)

  also have "\<dots> = insert 0 (set ns)"
    using \<open>sorted_wrt (<) (0 # ns)\<close>
    by (auto simp: decr_Suc) (use decr.elims in blast)

  finally show ?case
    by simp
next
  case (3 n ns \<sigma>' x xs)

  have IH: "index (rebuild (map decr (Suc n # ns)) \<sigma>' xs) ` X = set (map decr (Suc n # ns))"
  proof (intro "3.IH", goal_cases)
    case 1
    from \<open>sorted_wrt (<) (Suc n # ns)\<close> show ?case
      by (intro map_decr_sorted_wrt) auto
  next
    case 3
    from "3.prems" show ?case
      by (intro map_decr_gt) auto
  qed (use "3.prems" in auto)

  from \<open>set (x # xs) \<inter> X = {}\<close> have "x \<notin> X" "X \<inter> {x} = {}" by simp+

  then have "index (rebuild (Suc n # ns) \<sigma>' (x#xs)) ` X = Suc ` (index (rebuild (map decr (Suc n # ns)) \<sigma>' xs) ` X)"
    by auto

  also have "\<dots> = Suc ` (set (map decr (Suc n # ns)))"
    by (simp only: IH)

  finally show ?case
    using \<open>sorted_wrt (<) (Suc n # ns)\<close>
    by (auto simp: decr_Suc)
       (metis Suc_lessE decr.simps(2) image_iff)
next
  case ("4_1" n ns \<sigma>')

  then have "length (Suc n#ns) \<le> last (Suc n#ns)"
    by (intro sorted_strict_last_geq_length) auto

  with "4_1" show ?case
    by (metis add.right_neutral last_in_set leD list.distinct(1) list.size(3))
next
  case ("4_2" ns xs)
  then show ?case
    by auto
next
  case ("4_3" n ns)
  then show ?case
    by simp
next
  case ("4_4" v \<sigma>' xs)
  then show ?case
    by simp
next
  case ("4_5" n ns v \<sigma>')

  then have "length (Suc n#ns) \<le> last (Suc n#ns)"
    by (intro sorted_strict_last_geq_length) auto

  with "4_5" show ?case
    by (metis add.right_neutral last_in_set leD list.distinct(1) list.size(3))
qed


lemma card_restrict_permutation_eq_choose:
  assumes "finite V"
  assumes "X \<subseteq> V"
  assumes "\<sigma>' \<in> permutations_of_set X"
    \<comment> \<open>choose positions of X (the vertices we care about), the remaining vertices have arbitrary order\<close>
  shows "card {\<sigma> \<in> permutations_of_set V. [v <- \<sigma>. v \<in> X] = \<sigma>'} = (card V choose card X) * fact (card V - card X)" (is "?L = ?R")
proof -
  have "?L = card {(xs, vs). xs \<subseteq> {0..<card V} \<and> card xs = card X \<and> vs \<in> permutations_of_set (V - X)}"
  proof (intro bij_betw_same_card[where f = "\<lambda>\<sigma>. (index \<sigma> ` X, [v <- \<sigma>. v \<notin> X])"] 
              bij_betwI[where g = "\<lambda>(xs,vs). rebuild (sorted_list_of_set xs) \<sigma>' vs"], goal_cases)
    case 1    
    with assms show ?case
    proof (auto, goal_cases)
      case (1 \<sigma> x)
      then show ?case
        by (metis index_less_size_conv length_finite_permutations_of_set permutations_of_setD(1) subsetD)
    next
      case (2 \<sigma>)
      then show ?case
        by (intro card_image)
           (simp add: inj_on_def subset_eq permutations_of_setD)
    next
      case (3 \<sigma>)
      then show ?case
        by (auto intro!: permutations_of_setI dest: permutations_of_setD)
      qed
  next
    case 2
    with assms show ?case
    proof (auto, goal_cases)
      case (1 xs vs)
      then show ?case
      proof (intro permutations_of_setI, goal_cases)
        case 1
        then show ?case
        proof (intro set_rebuild_cong, goal_cases)
          case 1
          then show ?case 
            by (simp add: length_finite_permutations_of_set)
        next
          case 2
          with assms have "length \<sigma>' + length vs = card V"
            by (auto simp: length_finite_permutations_of_set card_Diff_subset[OF finite_subset] card_mono)

          with 2 show ?case
            by (auto simp: subset_eq_atLeast0_lessThan_finite)
        next
          case 3
          then show ?case
            by simp
        next
          case 4
          then show ?case
            by (auto dest: permutations_of_setD)
        qed

      next
        case 2
        then show ?case
          by (auto intro!: distinct_rebuild dest: permutations_of_setD)
      qed
    next
      case (2 xs vs)
      then show ?case
      proof (intro rebuild_filter_left, goal_cases)
        case 3
        then show ?case
          by (auto simp: subset_eq_atLeast0_lessThan_finite length_finite_permutations_of_set card_Diff_subset[OF finite_subset])
      qed (auto dest: permutations_of_setD length_finite_permutations_of_set)
    qed
  next
    case (3 \<sigma>)
    with \<open>\<sigma>' \<in> permutations_of_set X\<close> have "sorted_list_of_set (index \<sigma> ` X) = map (index \<sigma>) \<sigma>'"
      by (auto intro: sorted_list_of_set_is_map_index dest: permutations_of_setD)
    
    with 3 assms show ?case
      by (auto intro: rebuild_rebuilds[where V = V and X = X])
  next
    case (4 y)
    then obtain xs vs where "y = (xs,vs)" "xs \<subseteq> {0..<card V}" "card xs = card X" "vs \<in> permutations_of_set (V - X)"
      by blast

    have "index (rebuild (sorted_list_of_set xs) \<sigma>' vs) ` X = set (sorted_list_of_set xs)"
    proof (intro rebuild_indices, goal_cases)
      case 1
      then show ?case by auto
    next
      case 2
      from \<open>card xs = card X\<close> \<open>\<sigma>' \<in> permutations_of_set X\<close> \<open>finite V\<close> \<open>X \<subseteq> V\<close> show ?case
        by (auto simp: length_finite_permutations_of_set)
    next
      case 3
      from \<open>\<sigma>' \<in> permutations_of_set X\<close> \<open>vs \<in> permutations_of_set (V - X)\<close> \<open>finite V\<close> \<open>X \<subseteq> V\<close>
      have "length \<sigma>' + length vs = card V"
        by (auto simp: length_finite_permutations_of_set card_Diff_subset[OF finite_subset] card_mono)
      
      with \<open>xs \<subseteq> {0..<card V}\<close> show ?case
        by (auto simp: subset_eq_atLeast0_lessThan_finite)
    next
      case 4
      from \<open>vs \<in> permutations_of_set (V - X)\<close> show ?case
        by (auto dest: permutations_of_setD)
    next
      case 5
      from \<open>\<sigma>' \<in> permutations_of_set X\<close> show ?case
        by (auto dest: permutations_of_setD)
    next
      case 6
      from \<open>\<sigma>' \<in> permutations_of_set X\<close> show ?case
        by (auto dest: permutations_of_setD)
    qed

    also have "\<dots> = xs"
      using \<open>xs \<subseteq> {0..<card V}\<close>
      by (auto simp: subset_eq_atLeast0_lessThan_finite)

    finally have indices: "index (rebuild (sorted_list_of_set xs) \<sigma>' vs) ` X = xs" .

    from \<open>\<sigma>' \<in> permutations_of_set X\<close> \<open>vs \<in> permutations_of_set (V - X)\<close>
    have filter: "filter (\<lambda>v. v \<notin> X) (rebuild (sorted_list_of_set xs) \<sigma>' vs) = vs"
      by (auto intro!: rebuild_filter_right dest: permutations_of_setD)

    from \<open>y = (xs,vs)\<close> show ?case
      by (auto simp: indices filter)
  qed

  with assms show ?thesis
    by (simp add: card_perms_components)
qed

lemma card_restrict_permutation_eq_fact:
  assumes "finite V"
  assumes "X \<subseteq> V"
  assumes "\<sigma>' \<in> permutations_of_set X"
  shows "card {\<sigma> \<in> permutations_of_set V. [v <- \<sigma>. v \<in> X] = \<sigma>'} = fact (card V) / fact (card X)" (is "?L = ?R")
proof -
  from assms have choose_eq: "card V choose card X = fact (card V) / ((fact (card X) * fact (card V - card X)))"
    by (auto intro: binomial_fact card_mono)

  from assms have "?L = (card V choose card X) * fact (card V - card X)"
    by (simp add: card_restrict_permutation_eq_choose)

  also have "\<dots> = fact (card V) / (fact (card X) * fact (card V - card X)) * fact (card V - card X)"
    by (simp add: choose_eq)

  finally show ?thesis
    by simp
qed

locale wf_ranking =
  fixes G \<pi> V M

  assumes bipartite: "bipartite G (set \<pi>) V"
  assumes finite_graph: "finite G"
  assumes vertices: "Vs G = set \<pi> \<union> V"

  assumes max_card_matching: "max_card_matching G M"
begin

abbreviation "ranking_prob \<equiv> map_pmf (\<lambda>\<sigma>. ranking G \<pi> \<sigma>) (pmf_of_set (permutations_of_set V))"

lemma graph_abs_G[simp]: "graph_abs G"
  using finite_graph bipartite
  by (auto intro: finite_bipartite_graph_abs)

lemma graph_abs_M[simp]: "graph_abs M"
  using max_card_matching
  by (auto intro!: graph_abs_subgraph[OF graph_abs_G] dest: max_card_matchingD)

lemma finite[simp]: "finite V"
  using finite_graph vertices
  by (metis finite_Un graph_abs_G graph_abs_def)

lemma ranking_edgeE:
  assumes "e \<in> ranking G \<pi> \<sigma>"
  obtains u v where "e = {u,v}" "u \<in> set \<pi>" "v \<in> V" "v \<in> set \<sigma>"
  using assms bipartite
  by (smt (verit, best) bipartite_disjointD bipartite_edgeE disjoint_iff_not_equal edges_are_Vs(2) ranking_Vs_subset subgraph_ranking)

lemma bipartite_matching:
  "bipartite M (set \<pi>) V"
  using bipartite max_card_matching
  by (auto intro: bipartite_subgraph dest: max_card_matchingD)

lemma matching_if_perm: "\<sigma> \<in> permutations_of_set V \<Longrightarrow> matching (ranking G \<pi> \<sigma>)"
  using bipartite
  by (auto intro: matching_ranking dest: permutations_of_setD bipartite_disjointD)

lemma bipartite_if_perm: "\<sigma> \<in> permutations_of_set V \<Longrightarrow> bipartite (ranking G \<pi> \<sigma>) (set \<pi>) (set \<sigma>)"
  using bipartite
  by (auto dest: permutations_of_setD intro: bipartite_ranking)

lemma perms_of_V:
  shows "permutations_of_set V \<noteq> {}"
    and "finite (permutations_of_set V)"
  by (auto simp: finite)

end


locale ranking_on_perfect_matching = wf_ranking +
  assumes edge_exists:  "G \<noteq> {}"

  assumes perfect_matching: "perfect_matching G M"
begin

lemma non_empty: "V \<noteq> {}"
  using bipartite bipartite_edgeE edge_exists by blast

lemma non_empty_online[simp]: "\<pi> \<noteq> []"
  by (metis Un_empty bipartite bipartite_empty_part_iff_empty empty_set non_empty vertices vs_empty)

lemma offline_subset_vs: "v \<in> V \<Longrightarrow> v \<in> Vs G"
  using vertices by simp

lemma online_subset_vs: "u \<in> set \<pi> \<Longrightarrow> u \<in> Vs G"
  using vertices by simp

lemma the_match_offlineE:
  assumes "v \<in> V"
  obtains u where "{u,v} \<in> M" "u \<in> set \<pi>"
  by (smt (verit, ccfv_SIG) assms bipartite_disjointD bipartite_edgeE bipartite_matching disjoint_iff_not_equal empty_iff insert_iff offline_subset_vs perfect_matching perfect_matching_edgeE)

lemma the_match_onlineE:
  assumes "u \<in> set \<pi>"
  obtains v where "{u,v} \<in> M" "v \<in> V"
  by (smt (verit, ccfv_SIG) assms bipartite_disjointD bipartite_edgeE bipartite_matching empty_iff insertE insert_disjoint(1) mk_disjoint_insert online_subset_vs perfect_matching perfect_matching_edgeE)

lemma the_match_online:
  assumes "u \<in> set \<pi>"
  shows "{u, (THE v. {u,v} \<in> M)} \<in> M"
    and "(THE v. {u, v} \<in> M) \<in> V"
  using perfect_matching assms
  by (auto elim!: the_match_onlineE dest: perfect_matchingD the_match')

lemma the_match_offline:
  assumes "v \<in> V"
  shows "{(THE u. {u,v} \<in> M), v} \<in> M"
    and "(THE u. {u, v} \<in> M) \<in> set \<pi>"
  using perfect_matching assms
  by (auto elim!: the_match_offlineE dest: perfect_matchingD the_match)

lemma perfect_matching_bij:
  "bij_betw (\<lambda>u. (THE v. {u,v} \<in> M)) (set \<pi>) V"
  apply (rule bij_betwI[where g = "\<lambda>v. (THE u. {u,v} \<in> M)"])
     apply (auto intro: the_match_online the_match_offline)
   apply (rule the_equality)
    apply (rule the_match_online)
    apply blast
   apply (smt (verit, del_insts) insert_commute perfect_matching perfect_matchingD(2) the_match' the_match_online(1))
  apply (rule the_equality)
   apply (rule the_match_offline)
   apply blast
  apply (smt (verit) insert_commute perfect_matching perfect_matchingD(2) the_match the_match_offline(1))
  done

lemma card_online_eq_offline: "card (set \<pi>) = card V"
  using perfect_matching_bij
  by (auto intro: bij_betw_same_card)

definition random_permutation_t :: "nat \<Rightarrow> ('a list) pmf" where
  "random_permutation_t t \<equiv> 
    do {
      \<sigma> \<leftarrow> pmf_of_set (permutations_of_set V);
      v \<leftarrow> pmf_of_set V;
      return_pmf \<sigma>[v \<mapsto> t]
  }"

lemma random_permutation_geq_card:
  "card V \<le> t \<Longrightarrow> random_permutation_t t = random_permutation_t (card V - 1)"
  using perms_of_V
  unfolding random_permutation_t_def
  apply (auto intro!: pmf_eqI simp:)
  using finite non_empty
  apply (auto simp add: pmf_bind_pmf_of_set intro!: sum.cong)
  by (smt (verit) One_nat_def length_finite_permutations_of_set move_elem_to_gt_length permutations_of_setD(1) sum.cong)

lemma move_to_t_eq_uniform_less: "t < card V \<Longrightarrow> random_permutation_t t = pmf_of_set (permutations_of_set V)"
proof (rule pmf_eqI)
  fix \<sigma> :: "'a list"
  assume "t < card V"
  show "pmf (random_permutation_t t) \<sigma> = pmf (pmf_of_set (permutations_of_set V)) \<sigma>"
  proof (cases "\<sigma> \<in> permutations_of_set V")
    case True

    with \<open>t < card V\<close> have "t < length \<sigma>"
      by (simp add: length_finite_permutations_of_set)

    with True have set_eq: "{\<sigma>' \<in> permutations_of_set V. (card (V \<inter> {v. \<sigma> = \<sigma>'[v \<mapsto> t]})) = Suc 0} = {\<sigma>' \<in> permutations_of_set V. [x <- \<sigma>'. x \<noteq> (THE v. index \<sigma> v = t)] = [x <- \<sigma>. x \<noteq> (THE v. index \<sigma> v = t)]}"
      using permutations_move_to_eq_iff
      by auto

    from True \<open>t < length \<sigma>\<close> finite have "(\<Sum>xa\<in>permutations_of_set V. real (card (V \<inter> {xaa. \<sigma> = xa[xaa \<mapsto> t]}))) = real (card V)"
      by (intro sum_eq_card_where_One)
         (auto intro!: permutations_but_v_card[where t = t] 
           intro: index_nth_id simp: set_eq the_index[OF permutations_of_setD(2)] move_to_eq_iff dest: permutations_of_setD)

    with True finite non_empty \<open>t < length \<sigma>\<close> show ?thesis
      by (simp add: random_permutation_t_def pmf_bind_pmf_of_set indicator_singleton sum.If_cases
          flip: sum_divide_distrib)
  next
    case False
    with finite non_empty show ?thesis
      by (auto intro!: sum.neutral dest: permutation_move_to simp: random_permutation_t_def pmf_bind_pmf_of_set indicator_singleton sum.If_cases)
  qed
qed

lemma move_to_t_eq_uniform: "random_permutation_t t = pmf_of_set (permutations_of_set V)"
  by (cases "t < card V")
     (auto simp: random_permutation_geq_card card_gt_0_iff finite non_empty intro: move_to_t_eq_uniform_less)

abbreviation rank_unmatched :: "nat \<Rightarrow> bool pmf" where
  "rank_unmatched t \<equiv>
    do {
      \<sigma> \<leftarrow> pmf_of_set (permutations_of_set V);
      let R = ranking G \<pi> \<sigma>;
      return_pmf (\<sigma> ! t \<notin> Vs R)
    }"

abbreviation rank_matched :: "nat \<Rightarrow> bool pmf" where
  "rank_matched t \<equiv>
    do {
      \<sigma> \<leftarrow> pmf_of_set (permutations_of_set V);
      let R = ranking G \<pi> \<sigma>;
      return_pmf (\<sigma> ! t \<in> Vs R)
    }"

definition matched_before :: "nat \<Rightarrow> bool pmf" where
  "matched_before t \<equiv>
    do {
      \<sigma> \<leftarrow> pmf_of_set (permutations_of_set V);
      v \<leftarrow> pmf_of_set V;
      let R = ranking G \<pi> \<sigma>; 
      let u = (THE u. {u,v} \<in> M);     
      return_pmf (u \<in> Vs R \<and> index \<sigma> (THE v. {u,v} \<in> R) \<le> t)
    }"

lemma rank_matched_False_rank_unmatched_True[simplified]: "measure_pmf.prob (rank_matched t) {False} = measure_pmf.prob (rank_unmatched t) {True}"
  using perms_of_V
  by (simp add: measure_pmf_conv_infsetsum pmf_bind_pmf_of_set indicator_singleton)

lemma rank_matched_prob_is_expectation: "measure_pmf.prob (rank_matched t) {True} = measure_pmf.expectation (rank_matched t) of_bool"
  by (simp add: bernoulli_prob_True_expectation)

lemma perms_where_0th_matched_eq_perms: "permutations_of_set V \<inter> {\<sigma>. \<sigma> ! 0 \<in> Vs (ranking G \<pi> \<sigma>)} = permutations_of_set V"
proof (intro equalityI subsetI IntI CollectI)
  fix \<sigma>
  assume perm: "\<sigma> \<in> permutations_of_set V"
  show "\<sigma> ! 0 \<in> Vs (ranking G \<pi> \<sigma>)"
  proof (intro first_rank_always_matched[where G = G and \<pi> = \<pi> and M = "ranking G \<pi> \<sigma>"] ranking_matching_ranking)
    show "bipartite G (set \<pi>) (set \<sigma>)"
      using bipartite perm
      by (auto dest: permutations_of_setD)
  next
    show "\<sigma> \<noteq> []"
      using perm non_empty
      by (auto dest: permutations_of_setD)
  next
    show "\<sigma> ! 0 \<in> Vs G"
      by (metis card_gt_0_iff length_finite_permutations_of_set finite non_empty nth_mem offline_subset_vs perm permutations_of_setD(1))
  qed
qed blast

lemma first_rank_matched_prob_1: "measure_pmf.prob (rank_matched 0) {True} = 1"
  using perms_of_V
  by (auto simp: measure_pmf_conv_infsetsum pmf_bind_pmf_of_set indicator_singleton sum.If_cases perms_where_0th_matched_eq_perms)

lemma the_t:
  assumes "distinct xs"
  assumes "x \<in> set xs"
  shows "index xs x = (THE t. index xs x = t)"
    and "(THE t. index xs x = t) < length xs"
  using assms
  by (auto dest: theI'[OF distinct_Ex1])

lemma the_t_for_edge:
  assumes "\<sigma> \<in> permutations_of_set V"
  assumes "{u,v} \<in> G"
  assumes "u \<in> set \<pi>" "v \<in> set \<sigma>"
  shows "(THE t. \<exists>v'\<in>set \<sigma>. index \<sigma> v' = t \<and> v' \<in> {u,v}) = index \<sigma> v"
  using assms bipartite
  by (auto dest: permutations_of_setD bipartite_disjointD)

lemma v_unmatched_u_matched_before_Ex:
  assumes perm: "\<sigma> \<in> permutations_of_set V"
  assumes v: "v \<in> V"
  assumes "v \<notin> Vs (ranking G \<pi> \<sigma>[v \<mapsto> t])"
  shows "\<exists>v'. {(THE u. {u,v} \<in> M),v'} \<in> ranking G \<pi> \<sigma>[v \<mapsto> t][v \<mapsto> index \<sigma> v] \<and> index \<sigma>[v \<mapsto> t][v \<mapsto> index \<sigma> v] v' \<le> index \<sigma>[v \<mapsto> t] v"
proof (rule v_unmatched_edge_matched_earlier)
  show "(THE u. {u,v} \<in> M) \<in> set \<pi>"
    using v perfect_matching
    by (auto elim: the_match_offlineE dest: perfect_matchingD the_match)
next
  show "v \<in> set \<sigma>[v \<mapsto> t]"
    by (simp add: move_to_set)
next
  show "{THE u. {u,v} \<in> M, v} \<in> G"
    using v perfect_matching
    by (auto elim!: the_match_offlineE dest: perfect_matchingD the_match)
next
  show "v \<notin> Vs (ranking G \<pi> \<sigma>[v \<mapsto> t])"
    using assms by blast
next
  show "ranking_matching G (ranking G \<pi> \<sigma>[v \<mapsto> t]) \<pi> \<sigma>[v \<mapsto> t]"
    using perm v bipartite
    by (auto intro!: ranking_matching_ranking simp: move_to_set insert_absorb dest: permutations_of_setD)
next
  show "ranking_matching G (ranking G \<pi> \<sigma>[v \<mapsto> t][v \<mapsto> index \<sigma> v]) \<pi> \<sigma>[v \<mapsto> t][v \<mapsto> index \<sigma> v]"
    using perm v bipartite
    by (auto intro!: ranking_matching_ranking simp: move_to_set insert_absorb dest: permutations_of_setD)
qed

lemma v_unmatched_u_matched_before_the:
  assumes perm: "\<sigma> \<in> permutations_of_set V"
  assumes v: "v \<in> V"
  assumes "\<sigma>[v \<mapsto> t] ! t \<notin> Vs (ranking G \<pi> \<sigma>[v \<mapsto> t])"
  assumes "t < length \<sigma>"
  shows "(THE u. {u, v} \<in> M) \<in> Vs (ranking G \<pi> \<sigma>)"
    and "index \<sigma> (THE v'. {THE u. {u, v} \<in> M, v'} \<in> ranking G \<pi> \<sigma>) \<le> t"
proof -
  let ?u = "THE u. {u,v} \<in> M"
  have "\<sigma>[v \<mapsto> t] ! t = v"
    using assms
    by (auto intro: move_to_index_nth dest: permutations_of_setD)

  with assms obtain v' where v': "{?u, v'} \<in> ranking G \<pi> \<sigma>[v \<mapsto> t][v \<mapsto> index \<sigma> v]"
    "index \<sigma>[v \<mapsto> t][v \<mapsto> index \<sigma> v] v' \<le> index \<sigma>[v \<mapsto> t] v"
    by (auto dest: v_unmatched_u_matched_before_Ex)

  from perm v have move_to_move_to: "\<sigma>[v \<mapsto> t][v \<mapsto> index \<sigma> v] = \<sigma>"
    by (auto intro!: move_to_move_back_id dest: permutations_of_setD)

  with v' show "?u \<in> Vs (ranking G \<pi> \<sigma>)"
    by auto

  from v' perm have the_v': "(THE v'. {?u, v'} \<in> ranking G \<pi> \<sigma>) = v'"
    by (auto intro!: the_match' matching_if_perm simp: move_to_move_to)
  
  from assms have "index \<sigma>[v \<mapsto> t] v = t"
    by (auto intro: move_to_index_v dest: permutations_of_setD)

  with v' show "index \<sigma> (THE v'. {?u,v'} \<in> ranking G \<pi> \<sigma>) \<le> t"
    by (auto simp: the_v' move_to_move_to)
qed

lemma ranking_card_is_sum_of_matched_vertices:
  assumes \<sigma>: "\<sigma> \<in> permutations_of_set V"
  shows "card (ranking G \<pi> \<sigma>) = sum (\<lambda>t. of_bool (\<sigma> ! t \<in> Vs (ranking G \<pi> \<sigma>))) {..<card V}"
proof -
  have card_length: "card V = length \<sigma>"
    using assms
    by (simp add: length_finite_permutations_of_set)

  from \<sigma> have matching: "matching (ranking G \<pi> \<sigma>)"
    by (auto intro: matching_if_perm)

  from \<sigma> have bipartite': "bipartite (ranking G \<pi> \<sigma>) (set \<pi>) (set \<sigma>)"
    by (auto intro: bipartite_if_perm)

  have "card (ranking G \<pi> \<sigma>) = card (index \<sigma> ` \<Union> ((\<inter>) (set \<sigma>) ` ranking G \<pi> \<sigma>))"
  proof (rule bij_betw_same_card[of "\<lambda>e. (THE t. \<exists>v \<in> set \<sigma>. index \<sigma> v = t \<and> v \<in> e)"],
         rule bij_betwI[where g = "\<lambda>t. (THE e. e \<in> ranking G \<pi> \<sigma> \<and> \<sigma> ! t \<in> e)"])
    show "(\<lambda>e. THE t. \<exists>v\<in>set \<sigma>. index \<sigma> v = t \<and> v \<in> e) \<in> ranking G \<pi> \<sigma> \<rightarrow> index \<sigma> ` \<Union> ((\<inter>) (set \<sigma>) ` ranking G \<pi> \<sigma>)"
    proof (rule Pi_I)
      fix e
      assume edge: "e \<in> ranking G \<pi> \<sigma>"

      then obtain u v where uv: "e = {u,v}" "u \<in> set \<pi>" "v \<in> set \<sigma>"
        by (auto elim: ranking_edgeE)

      with \<sigma> edge have "(THE t. \<exists>v' \<in> set \<sigma>. index \<sigma> v' = t \<and> v' \<in> e) = index \<sigma> v"
        by (auto intro!: the_t_for_edge[simplified] dest: subgraph_ranking)

      with edge uv show "(THE t. \<exists>v \<in> set \<sigma>. index \<sigma> v = t \<and> v \<in> e) \<in> index \<sigma> ` \<Union> ((\<inter>) (set \<sigma>) ` ranking G \<pi> \<sigma>)"
        by (auto intro!: imageI)
    qed
  next
    show "(\<lambda>t. THE e. e \<in> ranking G \<pi> \<sigma> \<and> \<sigma> ! t \<in> e) \<in> index \<sigma> ` \<Union> ((\<inter>) (set \<sigma>) ` ranking G \<pi> \<sigma>) \<rightarrow> ranking G \<pi> \<sigma>"
    proof (rule Pi_I)
      fix t
      assume t: "t \<in> index \<sigma> ` \<Union> ((\<inter>) (set \<sigma>) ` ranking G \<pi> \<sigma>)"

      then obtain v where v: "index \<sigma> v = t" "v \<in> set \<sigma>" "v \<in> Vs (ranking G \<pi> \<sigma>)"
        by blast

      then obtain e where e: "e \<in> ranking G \<pi> \<sigma>" "v \<in> e"
        by (auto elim: vs_member_elim)

      with assms matching have the_e: "\<And>e'. e' \<in> ranking G \<pi> \<sigma> \<and> v \<in> e' \<Longrightarrow> e' = e"
        by (auto dest: matching_unique_match)

      with e v show "(THE e. e \<in> ranking G \<pi> \<sigma> \<and> \<sigma> ! t \<in> e) \<in> ranking G \<pi> \<sigma>"
        by (metis (no_types, lifting) nth_index theI')
    qed
  next
    show "\<And>e. e \<in> ranking G \<pi> \<sigma> \<Longrightarrow> (THE e'. e' \<in> ranking G \<pi> \<sigma> \<and> \<sigma> ! (THE t. \<exists>v \<in> set \<sigma>. index \<sigma> v = t \<and> v \<in> e) \<in> e') = e"
    proof -
      fix e
      assume e: "e \<in> ranking G \<pi> \<sigma>"

      then obtain u v where uv: "u \<in> set \<pi>" "v \<in> set \<sigma>" "e = {u,v}"
        by (auto elim: ranking_edgeE)

      then obtain t where t: "t = index \<sigma> v"
        by blast

      with uv \<sigma> bipartite have the_t: "(THE t. \<exists>v \<in> set \<sigma>. index \<sigma> v = t \<and> v \<in> e) = t"
        by (auto dest: bipartite_disjointD permutations_of_setD)

      from \<sigma> uv matching \<open>e \<in> ranking G \<pi> \<sigma>\<close> have the_e: "\<And>e'. e' \<in> ranking G \<pi> \<sigma> \<and> v \<in> e' \<Longrightarrow> e' = e"
        by (metis insertCI matching_unique_match)

      with e t \<open>v \<in> set \<sigma>\<close> show "(THE e'. e' \<in> ranking G \<pi> \<sigma> \<and> \<sigma> ! (THE t. \<exists>v \<in> set \<sigma>. index \<sigma> v = t \<and> v \<in> e) \<in> e') = e" 
        by (auto simp: the_t intro!: the_equality)
           (use \<open>e = {u,v}\<close> in blast)
    qed
  next
    show "\<And>t. t \<in> index \<sigma> ` \<Union> ((\<inter>) (set \<sigma>) ` ranking G \<pi> \<sigma>) \<Longrightarrow> (THE t'. \<exists>v \<in> set \<sigma>. index \<sigma> v = t' \<and> v \<in> (THE e. e \<in> ranking G \<pi> \<sigma> \<and> \<sigma> ! t \<in> e)) = t"
    proof (rule the_equality)
      fix t
      assume t: "t \<in> index \<sigma> ` \<Union> ((\<inter>) (set \<sigma>) ` ranking G \<pi> \<sigma>)"

      with matching show "\<exists>v \<in> set \<sigma>. index \<sigma> v = t \<and> v \<in> (THE e. e \<in> ranking G \<pi> \<sigma> \<and> \<sigma> ! t \<in> e)"
        by (auto simp: the_edge)
    next
      show "\<And>t t'. t \<in> index \<sigma> ` \<Union> ((\<inter>) (set \<sigma>) ` ranking G \<pi> \<sigma>) \<Longrightarrow> \<exists>v \<in> set \<sigma>. index \<sigma> v = t' \<and> v \<in> (THE e. e \<in> ranking G \<pi> \<sigma> \<and> \<sigma> ! t \<in> e) \<Longrightarrow> t' = t"
      proof -
        fix t t'
        assume t: "t \<in> index \<sigma> ` \<Union> ((\<inter>) (set \<sigma>) ` ranking G \<pi> \<sigma>)"
          and t': "\<exists>v \<in> set \<sigma>. index \<sigma> v = t' \<and> v \<in> (THE e. e \<in> ranking G \<pi> \<sigma> \<and> \<sigma> ! t \<in> e)"

        with \<sigma> matching bipartite' show "t' = t"
          by (auto simp: the_edge intro: bipartite_eqI)
      qed
    qed
  qed

  with \<sigma> bipartite' matching show ?thesis
    by (auto simp: card_length matched_indices_set_eq dest: permutations_of_setD)
qed

lemma rank_t_unmatched_prob_bound_matched_before:
  "t < card V \<Longrightarrow> measure_pmf.prob (rank_matched t) {False} \<le> measure_pmf.prob (matched_before t) {True}" (is "_ \<Longrightarrow> ?L \<le> ?R")
proof -
  assume "t < card V"
  include monad_normalisation

  have "?L = measure_pmf.prob (rank_unmatched t) {True}"
    by (simp add: rank_matched_False_rank_unmatched_True)

  also have "\<dots> = measure_pmf.prob (
    do {
      \<sigma> \<leftarrow> pmf_of_set (permutations_of_set V);
      v \<leftarrow> pmf_of_set V;
      let R = ranking G \<pi> \<sigma>[v \<mapsto> t];
      return_pmf (\<sigma>[v \<mapsto> t] ! t \<notin> Vs R)
    }) {True}"
    by (subst move_to_t_eq_uniform[symmetric, of t])
       (simp add: random_permutation_t_def)


  also have "\<dots> \<le> ?R"
    unfolding matched_before_def Let_def
    using perms_of_V finite non_empty
    by (intro bool_pmf_imp_prob_leq2)
       (auto simp: \<open>t < card V\<close> length_finite_permutations_of_set v_unmatched_u_matched_before_the)

  finally show ?thesis .
qed

lemma matched_before_uniform_u: "matched_before t = do
    {
      \<sigma> \<leftarrow> pmf_of_set (permutations_of_set V);
      u \<leftarrow> pmf_of_set (set \<pi>);
      let R = ranking G \<pi> \<sigma>;
      return_pmf (u \<in> Vs R \<and> index \<sigma> (THE v. {u,v} \<in> R) \<le> t)
    }"
  unfolding matched_before_def Let_def
  apply (rule pmf_eqI)
  using finite non_empty
  apply (simp add: pmf_bind_pmf_of_set indicator_singleton card_online_eq_offline sum.If_cases)
  apply (rule sum.cong)
   apply blast
  apply (rule arg_cong2[where f =  "(/)"])
   apply (simp)
   apply (rule bij_betw_same_card[where f = "\<lambda>v. (THE u. {u,v} \<in> M)"])
   apply (rule bij_betwI[where g = "\<lambda>u. (THE v. {u,v} \<in> M)"])
      apply (auto)
  using the_match_offline apply blast
  using the_match_online apply blast
       apply (metis perfect_matching perfect_matchingD(2) the_match the_match_online(1))
      apply (metis perfect_matching perfect_matchingD(2) the_match the_match_online(1))
     apply (metis perfect_matching perfect_matchingD(2) the_match the_match_online(1))
    apply (metis perfect_matching perfect_matchingD(2) the_match the_match_online(1))
  using perfect_matching perfect_matchingD(2) the_match' the_match_offline(1) apply fastforce
  using perfect_matching perfect_matchingD(2) the_match the_match_online(1) by fastforce

abbreviation "matched_before_t_set t \<equiv> 
  do {
    \<sigma> \<leftarrow> pmf_of_set (permutations_of_set V);
    let R = ranking G \<pi> \<sigma>;
    return_pmf {u \<in> set \<pi>. u \<in> Vs R \<and> index \<sigma> (THE v. {u,v} \<in> R) \<le> t}
  }"


lemma expected_size_matched_before_sum: "measure_pmf.expectation (matched_before_t_set t) card =
  (\<Sum>\<sigma>\<in>permutations_of_set V. card {u \<in> set \<pi>. u \<in> Vs (ranking G \<pi> \<sigma>) \<and> index \<sigma> (THE v. {u,v} \<in> ranking G \<pi> \<sigma>) \<le> t}) / fact (card V)" (is "?L = ?R")
proof -
have "?L = (\<Sum>\<^sub>aU. (\<Sum>\<sigma>\<in>permutations_of_set V. (if U = {u \<in> set \<pi>. u \<in> Vs (ranking G \<pi> \<sigma>) \<and> index \<sigma> (THE v. {u, v} \<in> ranking G \<pi> \<sigma>) \<le> t} then 1 else 0) / fact (card V)) * (card U))"
    using perms_of_V non_empty
    apply (simp add: pmf_expectation_eq_infsetsum pmf_bind Let_def indicator_singleton)
    apply (rule infsetsum_cong)
     apply (rule arg_cong2[where f = "(*)"])
      apply (rule infsetsum_sum_cong)
           apply (rule finite_subset[where B = "permutations_of_set V"])
    apply auto
    done

  also have "\<dots> = (\<Sum>U\<in>Pow(set \<pi>). (\<Sum>\<sigma>\<in>permutations_of_set V. (if U = {u \<in> set \<pi>. u \<in> Vs (ranking G \<pi> \<sigma>) \<and> index \<sigma> (THE v. {u,v} \<in> ranking G \<pi> \<sigma>) \<le> t} then 1 else 0) / fact (card V)) * (card U))"
    by (intro infsetsum_sum_cong)
       (auto intro!: finite_subset[where B = "Pow(set \<pi>)"] elim: sum.not_neutral_contains_not_neutral split: if_splits)

  also have "\<dots> = (\<Sum>\<sigma>\<in>permutations_of_set V. (\<Sum>U\<in>Pow(set \<pi>). (if U = {u \<in> set \<pi>. u \<in> Vs (ranking G \<pi> \<sigma>) \<and> index \<sigma> (THE v. {u,v} \<in> ranking G \<pi> \<sigma>) \<le> t} then 1 else 0) / fact (card V) * (card U)))"
    by (subst sum.swap)
       (simp add:  sum_distrib_right)

  also have "\<dots> = (\<Sum>\<sigma>\<in>permutations_of_set V. card {u \<in> set \<pi>. u \<in> Vs (ranking G \<pi> \<sigma>) \<and> index \<sigma> (THE v. {u,v} \<in> ranking G \<pi> \<sigma>) \<le> t} / fact (card V))"
    by (auto simp: mult_delta_left simp flip: sum_divide_distrib)

  finally show ?thesis
    by (auto simp: sum_divide_distrib)
qed


lemma matched_before_prob_is_expected_size_div: "measure_pmf.prob (matched_before t) {True} = measure_pmf.expectation (matched_before_t_set t) card / (card V)" (is "?L = ?R")
  using perms_of_V
  by (subst expected_size_matched_before_sum)
     (auto simp add: matched_before_uniform_u pmf_bind_pmf_of_set Let_def measure_pmf_conv_infsetsum
       card_online_eq_offline indicator_singleton sum.If_cases simp flip: sum_divide_distrib 
       intro!: sum.cong arg_cong2[where f = divide] bij_betw_same_card[where f = id] bij_betwI[where g = id])


lemma card_True: "card {x. x} = 1"
proof -
  have "{x. x} = {True}"
    by blast

  then show ?thesis
    by simp
qed

lemma matched_before_card_eq: "\<sigma> \<in> permutations_of_set V \<Longrightarrow> card {u\<in>set \<pi>. u \<in> Vs (ranking G \<pi> \<sigma>) \<and> index \<sigma> (THE v. {u,v} \<in> ranking G \<pi> \<sigma>) \<le> t} = card {v\<in>V. v \<in> Vs (ranking G \<pi> \<sigma>) \<and> index \<sigma> v \<le> t}"
proof (rule bij_betw_same_card[where f = "\<lambda>u. (THE v. {u,v} \<in> ranking G \<pi> \<sigma>)"],
       rule bij_betwI[where g = "\<lambda>v. (THE u. {u,v} \<in> ranking G \<pi> \<sigma>)"],
       goal_cases)
  case 1
  then show ?case
  proof (intro funcsetI)
    fix u
    assume "u \<in> {u \<in> set \<pi>. u \<in> Vs (ranking G \<pi> \<sigma>) \<and> index \<sigma> (THE v. {u, v} \<in> ranking G \<pi> \<sigma>) \<le> t}"

    then have u: "u \<in> set \<pi>" "u \<in> Vs (ranking G \<pi> \<sigma>)" "index \<sigma> (THE v. {u,v} \<in> ranking G \<pi> \<sigma>) \<le> t"
      by blast+

    then obtain v where v: "{u,v} \<in> ranking G \<pi> \<sigma>" "v \<in> V"
      by (smt (verit, best) bipartite bipartite_commute bipartite_eqI insertCI ranking_edgeE subgraph_ranking vs_member)

    with 1 have "(THE v. {u,v} \<in> ranking G \<pi> \<sigma>) = v"
      by (auto intro: the_match' dest: matching_if_perm)

    with u v show "(THE v. {u, v} \<in> ranking G \<pi> \<sigma>) \<in> {v \<in> V. v \<in> Vs (ranking G \<pi> \<sigma>) \<and> index \<sigma> v \<le> t}"
      by auto
  qed
next
  case 2
  then show ?case
  proof (intro funcsetI)
    fix v
    assume "v \<in> {v \<in> V. v \<in> Vs (ranking G \<pi> \<sigma>) \<and> index \<sigma> v \<le> t}"

    then have v: "v \<in> V" "v \<in> Vs (ranking G \<pi> \<sigma>)" "index \<sigma> v \<le> t"
      by blast+

    then obtain u where u: "{u,v} \<in> ranking G \<pi> \<sigma>" "u \<in> set \<pi>"
      by (smt (verit, best) bipartite bipartite_eqI insertCI ranking_edgeE subgraph_ranking vs_member)

    with 2 have "(THE u. {u,v} \<in> ranking G \<pi> \<sigma>) = u" "(THE v. {u,v} \<in> ranking G \<pi> \<sigma>) = v"
      by (auto intro: the_match the_match' dest: matching_if_perm)

    with u v show "(THE u. {u, v} \<in> ranking G \<pi> \<sigma>) \<in> {u \<in> set \<pi>. u \<in> Vs (ranking G \<pi> \<sigma>) \<and> index \<sigma> (THE v. {u, v} \<in> ranking G \<pi> \<sigma>) \<le> t}"
      by auto
  qed
next
  case (3 u)
  then have "u \<in> set \<pi>" "u \<in> Vs (ranking G \<pi> \<sigma>)"
    by blast+

  then obtain v where "{u,v} \<in> ranking G \<pi> \<sigma>"
    by (smt (verit, del_insts) bipartite bipartite_disjointD empty_iff insert_disjoint(1) insert_iff mk_disjoint_insert ranking_edgeE vs_member)

  with 3 have "(THE u. {u,v} \<in> ranking G \<pi> \<sigma>) = u" "(THE v. {u,v} \<in> ranking G \<pi> \<sigma>) = v"
    by (auto intro: the_match the_match' dest: matching_if_perm)

  then show ?case
    by simp
next
  case (4 v)
  then have "v \<in> V" "v \<in> Vs (ranking G \<pi> \<sigma>)"
    by blast+

  then obtain u where u: "{u,v} \<in> ranking G \<pi> \<sigma>"
    by (smt (verit, del_insts) bipartite bipartite_disjointD empty_iff insert_disjoint(1) insert_iff mk_disjoint_insert ranking_edgeE vs_member)

  with 4 have "(THE u. {u,v} \<in> ranking G \<pi> \<sigma>) = u" "(THE v. {u,v} \<in> ranking G \<pi> \<sigma>) = v"
    by (auto intro: the_match the_match' dest: matching_if_perm)

  then show ?case
    by simp
qed

lemma expected_size_matched_before_is_sum_of_probs: "t < card V \<Longrightarrow> measure_pmf.expectation (matched_before_t_set t) card = (\<Sum>s\<le>t. measure_pmf.prob (rank_matched s) {True})" (is "_ \<Longrightarrow> ?L = ?R")
proof -
  assume t: "t < card V"

  have "?L = (\<Sum>\<sigma>\<in>permutations_of_set V. (card {u\<in>set \<pi>. u \<in> Vs (ranking G \<pi> \<sigma>) \<and> index \<sigma> (THE v. {u,v} \<in> ranking G \<pi> \<sigma>) \<le> t})) / fact (card V)"
    by (simp add: expected_size_matched_before_sum)

  also have "\<dots> = (\<Sum>\<sigma>\<in>permutations_of_set V. (card {v\<in>V. v \<in> Vs (ranking G \<pi> \<sigma>) \<and> index \<sigma> v \<le> t})) / fact (card V)"
    by (simp add: matched_before_card_eq)

  also have "\<dots> = (\<Sum>\<sigma>\<in>permutations_of_set V. (\<Sum>s\<le>t. if (\<sigma> ! s \<in> Vs (ranking G \<pi> \<sigma>)) then 1 else 0)) / fact (card V)"
    using t
    apply (auto intro!: sum.cong simp: sum.If_cases)
    subgoal for \<sigma>
      apply (rule bij_betw_same_card[where f = "\<lambda>v. index \<sigma> v"])
      apply (rule bij_betwI[where g = "(!) \<sigma>"])
         apply (auto dest: permutations_of_setD)
        apply (metis length_finite_permutations_of_set nth_mem order_le_less_trans permutations_of_setD(1))
      apply (simp add: index_nth_id length_finite_permutations_of_set permutations_of_setD(2))
      by (simp add: index_nth_id length_finite_permutations_of_set permutations_of_setD(2))
    done

  also have "\<dots> = ?R"
    using perms_of_V
    by (subst sum.swap)
       (simp add: bernoulli_prob_True_expectation pmf_expectation_eq_infsetsum pmf_bind_pmf_of_set indicator_singleton mult_delta_left card_True sum.If_cases flip: sum_divide_distrib)

  finally show ?thesis .
qed

\<comment> \<open>Lemma 5 from paper\<close>
lemma rank_t_unmatched_prob_bound: "t < card V \<Longrightarrow> 1 - measure_pmf.prob (rank_matched t) {True} \<le> 1 / (card V) * (\<Sum>s\<le>t. measure_pmf.prob (rank_matched s) {True})" (is "_ \<Longrightarrow> ?L \<le> ?R")
proof -
  assume t: "t < card V"

  obtain p where "rank_matched t = bernoulli_pmf p" "0 \<le> p" "p \<le> 1"
    using bool_pmf_is_bernoulli_pmf by blast

  then have "?L = measure_pmf.prob (rank_matched t) {False}"
    by (auto simp: measure_pmf_conv_infsetsum)

  also have "\<dots> \<le> measure_pmf.prob (matched_before t) {True}"
    using t
    by (intro rank_t_unmatched_prob_bound_matched_before)

  also have "\<dots> = measure_pmf.expectation (matched_before_t_set t) card / (card V)"
    by (simp add: matched_before_prob_is_expected_size_div)

  also have "\<dots> = ?R"
    using t
    by (simp add: expected_size_matched_before_is_sum_of_probs)

  finally show "?L \<le> ?R" .
qed

lemma expected_size_is_sum_of_matched_ranks: "measure_pmf.expectation ranking_prob card = (\<Sum>s<card V. measure_pmf.prob (rank_matched s) {True})"
proof -
  from perms_of_V have "measure_pmf.expectation ranking_prob card = (\<Sum>\<sigma>\<in>permutations_of_set V. (card (ranking G \<pi> \<sigma>))) / fact (card V)"
    by (auto simp: integral_pmf_of_set)

  also have "\<dots> = (\<Sum>\<sigma>\<in>permutations_of_set V. \<Sum>t<card V. of_bool (\<sigma> ! t \<in> Vs (ranking G \<pi> \<sigma>))) / fact (card V)"
    using ranking_card_is_sum_of_matched_vertices
    by auto

  also have "\<dots> = measure_pmf.expectation (pmf_of_set (permutations_of_set V)) (\<lambda>\<sigma>. \<Sum>t<card V. of_bool (\<sigma> ! t \<in> Vs (ranking G \<pi> \<sigma>)))"
    using perms_of_V
    by (auto simp: integral_pmf_of_set)

  also have "\<dots> = (\<Sum>t<card V. measure_pmf.expectation (pmf_of_set (permutations_of_set V)) (\<lambda>\<sigma>. of_bool (\<sigma> ! t \<in> Vs (ranking G \<pi> \<sigma>))))"
    using expectation_sum_pmf_of_set[OF perms_of_V]
    by fast

  also have "\<dots> = (\<Sum>t<card V. measure_pmf.prob (rank_matched t) {True})"
    by (subst rank_matched_prob_is_expectation)
       (use perms_of_V in \<open>auto simp add: pmf_expectation_bind_pmf_of_set integral_pmf_of_set divide_inverse\<close>)

  finally show ?thesis .
qed

lemma comp_ratio_no_limit: "measure_pmf.expectation ranking_prob card / (card V) \<ge> 1 - (1 - 1/(card V + 1)) ^ (card V)" (is "?L \<ge> ?R")
proof -
  have "?R = ((card V) - (card V) * (1 - 1 / (card V + 1))^(card V)) / card V"
    by (auto simp: diff_divide_distrib)

  also have "\<dots> = ((card V) - (card V) * (card V / (card V + 1)) ^ (card V)) / card V"
    by (simp add: field_simps)

  also have "\<dots> = (\<Sum>s<card V. (1 - 1/(card V + 1))^(s+1)) / card V"
    by (simp only: sum_gp_strict_Suc)

  also have "\<dots> = (\<Sum>s\<le>card V - 1. (1 - 1/(real (card V) + 1))^(s+1)) / card V"
    using non_empty
    by (auto simp: ac_simps simp del: finite)
       (metis (mono_tags, lifting) Suc_pred lessThan_Suc_atMost)

  also have "\<dots> \<le> (\<Sum>s\<le>card V - 1. measure_pmf.prob (rank_matched s) {True}) / card V"
    using non_empty finite
    by (intro divide_right_mono bounded_by_sum_bounds_sum rank_t_unmatched_prob_bound)
       (auto simp: first_rank_matched_prob_1[simplified] card_gt_0_iff)

  also have "\<dots> = ?L"
    by (subst expected_size_is_sum_of_matched_ranks)
       (metis (no_types, lifting) One_nat_def Suc_pred card_gt_0_iff lessThan_Suc_atMost local.finite non_empty)

  finally show ?thesis .
qed

end (* locale ranking_on_perfect_matching *)


lemma sum_split:
  assumes "finite A" "finite B"
  assumes "\<Union>(g ` A) = B"
  assumes "\<And>x x'. x \<in> A \<Longrightarrow> x' \<in> A \<Longrightarrow> x \<noteq> x' \<Longrightarrow> g x \<inter> g x' = {}"
  shows "(\<Sum>x\<in>A. (\<Sum>y\<in>g x. f y)) = (\<Sum>y\<in>B. f y)"
  using assms
  by (smt (verit, ccfv_SIG) finite_UN sum.UNION_disjoint sum.cong)

context wf_ranking
begin

lemma expectation_make_perfect_matching_le:
  assumes "G' = make_perfect_matching G M"
  shows "measure_pmf.expectation (map_pmf (\<lambda>\<sigma>. ranking G' \<pi> \<sigma>) (pmf_of_set (permutations_of_set (V \<inter> Vs G')))) card \<le>
    measure_pmf.expectation ranking_prob card" (is "?L \<le> ?R")
proof -
  have "?R = (\<Sum>\<sigma>\<in>permutations_of_set V. card (ranking G \<pi> \<sigma>) / fact (card V))"
    using perms_of_V
    by (auto simp: integral_pmf_of_set sum_divide_distrib)

  also have "\<dots> = (\<Sum>\<sigma>'\<in>permutations_of_set (V \<inter> Vs G'). (\<Sum>\<sigma>\<in>{\<sigma>\<in>permutations_of_set V. \<sigma> \<setminus> (V - (V \<inter> Vs G')) = \<sigma>'}. card (ranking G \<pi> \<sigma>) / fact (card V)))"
    by (rule sum_split[symmetric], auto; intro permutations_of_setI)
       (auto simp: remove_vertices_set dest: permutations_of_setD remove_vertices_distinct)

  also have "\<dots> \<ge> (\<Sum>\<sigma>'\<in>permutations_of_set (V \<inter> Vs G'). (\<Sum>\<sigma>\<in>{\<sigma>\<in>permutations_of_set V. \<sigma> \<setminus> (V - (V \<inter> Vs G')) = \<sigma>'}. card (ranking G' \<pi> \<sigma>) / fact (card V)))" (is "_ \<ge> ?S")
    unfolding assms
    apply (auto intro!: sum_mono divide_right_mono)
    subgoal for \<sigma>
      using bipartite
        bipartite_subgraph[OF bipartite subgraph_make_perfect_matching, of M]
      by (auto intro!: ranking_matching_card_leq_on_perfect_matching_graph[of G _ \<pi> \<sigma> M] ranking_matching_ranking dest: permutations_of_setD)
    done

  finally have "?S \<le> ?R" .

  have "?S = (\<Sum>\<sigma>'\<in>permutations_of_set (V \<inter> Vs G'). (\<Sum>\<sigma>\<in>{\<sigma>\<in>permutations_of_set V. \<sigma> \<setminus> (V - (V \<inter> Vs G')) = \<sigma>'}. card (ranking G' \<pi> \<sigma>') / fact (card V)))"
    by (intro sum.cong arg_cong2[where f = "(/)"] arg_cong[where f = card] arg_cong[where f = real])
       (auto intro!: ranking_remove_vertices_not_in_graph_ranking[symmetric])

  also have "\<dots> = (\<Sum>\<sigma>'\<in>permutations_of_set (V \<inter> Vs G'). (\<Sum>\<sigma>\<in>{\<sigma>\<in>permutations_of_set V. filter (\<lambda>v. v \<in> V \<inter> Vs G') \<sigma> = \<sigma>'}. card (ranking G' \<pi> \<sigma>') / fact (card V)))"
    apply (intro sum.cong)
      apply (auto simp: remove_vertices_list_def)
     apply (intro filter_cong)
      apply (auto dest: permutations_of_setD)
    apply (intro filter_cong)
     apply (auto dest: permutations_of_setD)
    done

  also have "\<dots> = (\<Sum>\<sigma>'\<in>permutations_of_set (V \<inter> Vs G'). (fact (card V) / fact (card (V \<inter> Vs G'))) * real (card (ranking G' \<pi> \<sigma>')) / fact (card V))"
    apply (rule sum.cong)
     apply blast
    apply (simp only: sum_constant times_divide_eq_right)
    apply (rule arg_cong2[where f = "(/)"])
     apply (rule arg_cong2[where f = "(*)"])
    apply (intro card_restrict_permutation_eq_fact)
        apply (auto)
    done

  also have "\<dots> = (\<Sum>\<sigma>'\<in>permutations_of_set (V \<inter> Vs G'). card (ranking G' \<pi> \<sigma>') / fact (card (V \<inter> Vs G')))"
    by simp

  also have "\<dots> = ?L"
    using perms_of_V
    by (auto simp: integral_pmf_of_set sum_divide_distrib)

  finally have "?S = ?L" .

  with \<open>?S \<le> ?R\<close> show "?L \<le> ?R"
    by linarith
qed


theorem "measure_pmf.expectation ranking_prob card / (card M) \<ge> 1 - (1 - 1/(card M + 1)) ^ (card M)"
proof (cases "G = {}")
  case True
  with max_card_matching have "M = {}"
    by (auto dest: max_card_matchingD)

  then show ?thesis
    by auto
next
  case False

  have "M \<noteq> {}"
    by (rule max_card_matching_non_empty)
       (use max_card_matching False in \<open>auto\<close>)

  define G' where "G' \<equiv> make_perfect_matching G M"

  then have "G' \<subseteq> G"
    by (auto simp: subgraph_make_perfect_matching)

  with bipartite have bipartite_G': "bipartite G' (set \<pi>) V"
    by (auto intro: bipartite_subgraph)

  have perfect_in_G': "perfect_matching G' M"
      unfolding G'_def
      using finite_graph max_card_matching
      by (intro perfect_matching_make_perfect_matching)
         (auto dest: max_card_matchingD)

  have bipartite_G': "bipartite G' (set [u <- \<pi>. u \<in> Vs G']) (V \<inter> Vs G')"
  proof (intro bipartiteI)
    fix e assume e: "e \<in> G'"
    then obtain u v where e_in_G: "e = {u,v}" "u \<in> set \<pi>" "v \<in> V"
      unfolding G'_def
      using bipartite
      by (auto dest!: subgraph_make_perfect_matching[THEN subsetD] elim: bipartite_edgeE)

    with e have "u \<in> Vs G'" "v \<in> Vs G'"
      by blast+

    with e_in_G show "\<exists>u v. e = {u,v} \<and>  u \<in> set [u <- \<pi>. u \<in> Vs G'] \<and> v \<in> V \<inter> Vs G'"
      by auto
  qed (use bipartite in \<open>auto dest: bipartite_disjointD\<close>)

  from bipartite_G' have vs_G':  "Vs G' = (set [u <- \<pi>. u \<in> Vs G']) \<union> (V \<inter> Vs G')"
    by (auto simp: vs_make_perfect_matching dest: bipartite_vertex)

  with perfect_in_G' bipartite_G' have card_eq: "card (V \<inter> Vs G') = card M"
    by (auto dest: perfect_matching_bipartite_card_eq)

  interpret pm: ranking_on_perfect_matching "G'" "[u <- \<pi>. u \<in> Vs G']" "V \<inter> Vs G'"
  proof (unfold_locales)
    show "bipartite G' (set [u <- \<pi>. u \<in> Vs G']) (V \<inter> Vs G')"
      using bipartite_G' by blast
  next
    show "finite G'"
      using finite_graph \<open>G' \<subseteq> G\<close>
      by (auto intro: finite_subset)
  next
    show "max_card_matching G' M"
      unfolding G'_def
      using max_card_matching
      by (auto intro!: max_card_matching_make_perfect_matching dest: max_card_matchingD
               intro: graph_abs.finite_E)

    with \<open>M \<noteq> {}\<close> show "G' \<noteq> {}"
      by (auto dest: max_card_matchingD)
  next
    show "Vs G' = (set [u <- \<pi>. u \<in> Vs G']) \<union> (V \<inter> Vs G')"
      using vs_G' by blast
  next
    show "perfect_matching G' M"
      using \<open>perfect_matching G' M\<close> by blast
  qed

  from pm.non_empty have non_empty: "V \<noteq> {}" by blast

  have "measure_pmf.expectation pm.ranking_prob card \<le> measure_pmf.expectation ranking_prob card"
    using G'_def
    by (simp only: ranking_filter_vs)
       (rule expectation_make_perfect_matching_le, blast)

  have "1 - (1 - (1/(card M + 1)))^(card M) \<le> measure_pmf.expectation pm.ranking_prob card / card M"
    using pm.comp_ratio_no_limit[simplified card_eq]
    by blast

  also have "\<dots> \<le> measure_pmf.expectation ranking_prob card / card M"
    using G'_def
    by (simp only: ranking_filter_vs, intro divide_right_mono expectation_make_perfect_matching_le)
       auto
  
  finally show ?thesis .
qed

end
end
