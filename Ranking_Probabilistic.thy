theory Ranking_Probabilistic
  imports
    Ranking2
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

fun move_to_alt :: "'a list \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a list" where
  "move_to_alt [] v n = [v]"
| "move_to_alt xs v 0 = v # [x <- xs. x \<noteq> v]"
| "move_to_alt (x#xs) v (Suc n) = (if v = x then move_to_alt xs v (Suc n) else x # move_to_alt xs v n)"

lemma distinct_move_to_alt_def: "distinct xs  \<Longrightarrow> xs[v \<mapsto> t] = move_to_alt xs v t"
  by (induction xs v t rule: move_to_alt.induct)
     (auto simp: move_to_Nil move_to_0 move_to_Cons_Suc move_to_Cons_eq)

lemma distinct_same_order_list_eq:
  assumes "distinct xs" "distinct xs'"
  assumes "set xs = set xs'"
  assumes "\<forall>x y. index xs x \<le> index xs y \<longleftrightarrow> index xs' x \<le> index xs' y"
  shows "xs = xs'"
  using assms
proof (induction xs xs' rule: list_induct2')
  case (4 x xs x' xs')
  then have "x = x'"
    by (auto split: if_splits)

  from 4 have distinct: "distinct xs" "distinct xs'"
    by simp_all

  from 4 have "\<forall>x y. (index xs x \<le> index xs y) = (index xs' x \<le> index xs' y)"
    by (auto split: if_splits)
       (metis index_conv_size_if_notin index_le_size index_less_size_conv insert_eq_iff linorder_not_le)+

  with 4 distinct \<open>x = x'\<close> show ?case
    by fastforce
qed auto

lemma list_eq_same_order:
  assumes "xs = xs'"
  shows "\<forall>x y. index xs x \<le> index xs y \<longleftrightarrow> index xs' x \<le> index xs' y"
  using assms
  by blast

lemma move_to_filter_eq: "[x <- xs. x \<noteq> v][v \<mapsto> t] = xs[v \<mapsto> t]"
  by (metis filter_id_conv filter_set member_filter move_to_def)

lemma distinct_order_filter_eq:
  assumes "distinct xs" "distinct xs'"
  assumes "set xs = set xs'"
  assumes "\<forall>x y. x \<noteq> v \<and> y \<noteq> v \<longrightarrow> (index xs x \<le> index xs y \<longleftrightarrow> index xs' x \<le> index xs' y)"
  shows "[x <- xs. x \<noteq> v] = [x <- xs'. x \<noteq> v]"
  using assms
  apply (intro distinct_same_order_list_eq)
     apply (auto)
   apply (metis (mono_tags, lifting) index_filter_neq index_less_in_set index_less_size_conv leD leI mem_Collect_eq set_filter size_index_conv)+
  done

lemma distinct_filter_eq_order:
  assumes "distinct xs" "distinct xs'"
  assumes "set xs = set xs'"
  assumes "[x <- xs. x \<noteq> v] = [x <- xs'. x \<noteq> v]"
  shows "\<forall>x y. x \<noteq> v \<and> y \<noteq> v \<longrightarrow> (index xs x \<le> index xs y \<longleftrightarrow> index xs' x \<le> index xs' y)"
  using assms
  by auto (metis index_filter_neq)+

lemma distinct_move_to_eq_if:
  assumes "distinct xs" "distinct xs'"
  assumes "set xs = set xs'"
  assumes "v \<in> set xs" "index xs v = t"
  assumes "\<forall>x y. x \<noteq> v \<and> y \<noteq> v \<longrightarrow> (index xs x \<le> index xs y \<longleftrightarrow> index xs' x \<le> index xs' y)"
  shows "xs'[v \<mapsto> t] = xs"
  using assms
  by (smt (verit, ccfv_SIG) distinct_count_in_set distinct_order_filter_eq move_to_def move_to_id)

lemma distinct_move_to_indices_if_eq:
  assumes "xs'[v \<mapsto> t] = xs"
  shows "\<forall>x y. x \<noteq> v \<and> y \<noteq> v \<longrightarrow> (index xs x \<le> index xs y \<longleftrightarrow> index xs' x \<le> index xs' y)"
  by (metis assms move_to_others_leq)

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
proof (rule)
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

lemma bipartite_edge_In_Ex1:
  assumes "bipartite M U V"
  assumes "matching M"
  assumes "e \<in> M"
  shows "\<exists>!e'. e' \<in> M \<and> V \<inter> e \<subseteq> e'"
  using assms
  by auto
     (smt (verit, best) bipartite_edgeE disjoint_insert(1) in_mono inf_bot_right le_iff_inf matching_unique_match)+

lemma the_bipartite_edge_In:
  assumes "bipartite M U V"
  assumes "matching M"
  assumes "e \<in> M"
  shows "(THE e'. e' \<in> M \<and> V \<inter> e \<subseteq> e') = e"
proof (rule ccontr)
  assume neq: "(THE e'. e' \<in> M \<and> V \<inter> e \<subseteq> e') \<noteq> e"

  obtain e' where e': "e' \<in> M" "V \<inter> e \<subseteq> e'"
    using bipartite_edge_In_Ex1 assms
    by blast

  with assms bipartite_edge_In_Ex1 have the_e': "(THE e'. e' \<in> M \<and> V \<inter> e \<subseteq> e') = e'"
    by (intro the1_equality) blast+

  with neq assms e' bipartite_edge_In_Ex1 show False
    by blast
qed

lemma card_bipartite_matching_In:
  assumes "bipartite M U V"
  assumes "matching M"
  shows "card M = card (((\<inter>) V) ` M)"
  using assms
  by (auto intro!: bij_betw_same_card[of "(\<inter>) V"] intro: bij_betwI[where g = "\<lambda>v. (THE e. e \<in> M \<and> v \<subseteq> e)"]
      simp: the_bipartite_edge_In)

lemma card_singleton_UN:
  assumes "\<forall>x \<in> X. \<exists>y. x = {y}"
  shows "card (\<Union> X) = card X"
  using assms
  by (auto intro!: bij_betw_same_card[of "\<lambda>x. {x}"] intro!: bij_betwI[where g = "\<lambda>X. (THE x. X = {x})"])

lemma bipartite_In_singletons:
  assumes "bipartite G U V"
  assumes "X \<in> ((\<inter>) V) ` G"
  shows "\<exists>x. X = {x}"
  using assms
  by (auto elim!: bipartite_edgeE dest: bipartite_disjointD)


lemma distinct_indexE:
  assumes "distinct xs"
  assumes "t < length xs"
  obtains x where "index xs x = t" "(THE x. index xs x = t) = x" "x \<in> set xs"
  using assms index_nth_id
  by (smt (verit, ccfv_threshold) index_less_size_conv nth_index the_equality)


lemma matched_indices_set_eq:
  assumes "bipartite M U (set xs)"
  assumes "distinct xs"
  assumes "matching M"
  shows "{..<length xs} \<inter> {t. (THE v. index xs v = t) \<in> Vs M} = (index xs) ` \<Union> (((\<inter>) (set xs)) ` M)"
  using assms
  by (auto elim: distinct_indexE intro!: rev_image_eqI simp: Vs_def)

lemma the_edge:
  assumes "matching M"
  assumes "e \<in> M"
  assumes "v \<in> e"
  shows "(THE e. e \<in> M \<and> v \<in> e) = e"
  using assms
  by (auto intro!: the_equality dest: matching_unique_match)

lemma bipartite_eqI:
  assumes "bipartite M U V"
  assumes "e \<in> M"
  assumes "x \<in> e" "x \<in> V" "y \<in> e" "y \<in> V"
  shows "x = y"
  using assms
  by (smt (verit, best) IntE bipartite_disjointD bipartite_edgeE disjoint_iff_not_equal insert_iff)

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

lemma indicator_singleton: "indicator {x} y = (if  x = y then 1 else 0)"
  by (auto simp add: indicator_eq_1_iff)

lemma sum_union:
  assumes "B \<union> C = A"
  shows "sum f A = sum f (B \<union> C)"
  using assms by blast

lemma sum_eq_card_where_One:
  assumes "finite A"
  assumes "card {x \<in> A. f x = 1} = n"
  assumes "\<forall>x. f x \<noteq> 0 \<longrightarrow> f x = 1"
  shows "sum f A = real n"
proof -
  have "sum f A = sum f ({a \<in> A. f a = 0} \<union> {a \<in> A. f a \<noteq> 0})"
    by (auto intro: sum_union)

  also have "\<dots> = sum f {a \<in> A. f a = 0} + sum f {a \<in> A. f a \<noteq> 0}"
    by (rule sum.union_disjoint)
       (insert \<open>finite A\<close>, auto)

  also have "\<dots> = sum f {a \<in> A. f a \<noteq> 0}"
    by (auto intro!: sum.neutral)

  also have "\<dots> = sum f {a \<in> A. f a = 1}"
    using \<open>\<forall>x. f x \<noteq> 0 \<longrightarrow> f x = 1\<close>
    by (metis zero_neq_one)

  also have "\<dots> = n"
    using assms
    by simp

  finally show ?thesis .
qed

lemma pmf_of_perms_finite_support:
  assumes "finite V"
  shows  "finite (set_pmf (pmf_of_set (permutations_of_set V)))"
  using assms
  by simp

context includes monad_normalisation
begin

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

end
locale ranking_on_perfect_matching =
  fixes G V M \<pi>
  assumes bipartite: "bipartite G (set \<pi>) V"
  assumes finite: "finite V"
  assumes non_empty: "V \<noteq> {}"

  assumes perfect_matching: "perfect_matching G M"
begin

lemma ranking_edgeE:
  assumes "e \<in> ranking G \<pi> \<sigma>"
  obtains u v where "e = {u,v}" "u \<in> set \<pi>" "v \<in> V" "v \<in> set \<sigma>"
  using assms bipartite
  by (smt (verit, best) bipartite_disjointD bipartite_edgeE disjoint_iff_not_equal edges_are_Vs(2) ranking_Vs_subset subgraph_ranking)

lemma bipartite_matching:
  "bipartite M (set \<pi>) V"
  using bipartite perfect_matching
  by (auto intro: bipartite_subgraph dest: perfect_matchingD)

lemma the_perfect_match:
  assumes "v \<in> Vs G" "v \<in> V"
  obtains u where "{u,v} \<in> M" "u \<in> set \<pi>"
  using assms perfect_matching bipartite_matching  
  apply (auto elim!: perfect_matching_edgeE bipartite_edgeE dest: bipartite_disjointD)
  by (smt (verit, del_insts) bipartite_def disjoint_iff_not_equal insertE perfect_matching perfect_matching_edgeE singletonD)

abbreviation "ranking_prob \<equiv> map_pmf (\<lambda>\<sigma>. ranking G \<pi> \<sigma>) (pmf_of_set (permutations_of_set V))"

lemma graph_absG: "graph_abs G"
  using bipartite finite
  by (auto intro: finite_bipartite_graph_abs)

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
  apply (auto intro!: pmf_eqI simp: pmf_bind_pmf_of_set)
  using finite non_empty
  apply (auto simp add: pmf_bind_pmf_of_set  intro!: sum.cong)
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
         (auto intro!: sum_eq_card_where_One permutations_but_v_card[where t = t] 
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
      let M = ranking G \<pi> \<sigma>;
      return_pmf ((THE v. index \<sigma> v = t) \<notin> Vs M)
    }"

abbreviation rank_matched :: "nat \<Rightarrow> bool pmf" where
  "rank_matched t \<equiv>
    do {
      \<sigma> \<leftarrow> pmf_of_set (permutations_of_set V);
      let M = ranking G \<pi> \<sigma>;
      return_pmf ((THE v. index \<sigma> v = t) \<in> Vs M)
    }"

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

lemma rank_matched_prob_is_expectation: "measure_pmf.prob (rank_matched t) {True} = measure_pmf.expectation (rank_matched t) of_bool"
  by (simp add: bernoulli_prob_True_expectation)

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

lemma ranking_card_is_sum_of_matched_vertices:
  assumes \<sigma>: "\<sigma> \<in> permutations_of_set V"
  shows "card (ranking G \<pi> \<sigma>) = sum (\<lambda>t. of_bool ((THE v. index \<sigma> v = t) \<in> Vs (ranking G \<pi> \<sigma>))) {..<card V}"
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

lemma rank_t_unmatched_prob_bound:
  "t < card V \<Longrightarrow> 1 - measure_pmf.prob (rank_matched t) {True} \<le> (\<Sum>s\<le>t. measure_pmf.prob (rank_matched s) {True})"
  sorry


lemma expected_size_is_sum_of_matched_ranks: "measure_pmf.expectation ranking_prob (\<lambda>M. real (card M)) = (\<Sum>s\<in>{..<card V}. measure_pmf.prob (rank_matched s) {True})"
proof -
  from perms_of_V have "measure_pmf.expectation ranking_prob (\<lambda>M. real (card M)) = real (\<Sum>\<sigma>\<in>permutations_of_set V. (card (ranking G \<pi> \<sigma>))) / fact (card V)"
    by (auto simp: integral_pmf_of_set)

  also have "\<dots> = real (\<Sum>\<sigma>\<in>permutations_of_set V. \<Sum>t\<in>{..<card V}. of_bool ((THE v. index \<sigma> v = t) \<in> Vs (ranking G \<pi> \<sigma>))) / fact (card V)"
    using ranking_card_is_sum_of_matched_vertices
    by auto

  also have "\<dots> = measure_pmf.expectation (pmf_of_set (permutations_of_set V)) (\<lambda>\<sigma>. \<Sum>t<card V. of_bool ((THE v. index \<sigma> v = t) \<in> Vs (ranking G \<pi> \<sigma>)))"
    using perms_of_V
    by (auto simp: integral_pmf_of_set)

  also have "\<dots> = (\<Sum>t<card V. measure_pmf.expectation (pmf_of_set (permutations_of_set V)) (\<lambda>\<sigma>. of_bool ((THE v. index \<sigma> v = t) \<in> Vs (ranking G \<pi> \<sigma>))))"
    using expectation_sum_pmf_of_set[OF perms_of_V]
    by fast

  also have "\<dots> = (\<Sum>t<card V. measure_pmf.prob (rank_matched t) {True})"
    by (subst rank_matched_prob_is_expectation)
       (use perms_of_V in \<open>auto simp add: pmf_expectation_bind_pmf_of_set integral_pmf_of_set divide_inverse\<close>)

  finally show ?thesis .
qed
end (* ranking_on_perfect_matching *)
end
