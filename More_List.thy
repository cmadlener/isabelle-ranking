theory More_List
  imports "List-Index.List_Index"
begin

sledgehammer_params [provers = cvc4 vampire verit e spass z3 zipperposition]

lemma index_gt_induct: 
  assumes "\<And>x. (\<And>y. (index xs y > index xs x \<Longrightarrow> P y)) \<Longrightarrow> P x"
  shows "P x"
  using assms
  by (induction "length xs - index xs x" arbitrary: x rule: less_induct)
     (metis diff_less_mono2 index_le_size le_less not_le)

lemma length_minus_index_less_index_gt:
  "length xs - index xs x < length xs - index xs x' \<longleftrightarrow> index xs x' < index xs x"
  by (induction xs) auto

lemma index_less_in_set: "index xs x < index xs x' \<Longrightarrow> x \<in> set xs"
  by (metis index_conv_size_if_notin index_le_size leD)

lemma transp_index_less: "transp (\<lambda>a b. index xs a < index xs b)"
  by (auto intro: transpI)

lemma sorted_wrt_index_less_distinct:
  "sorted_wrt (\<lambda>a b. index \<sigma> a < index \<sigma> b) xs \<Longrightarrow> distinct xs"
  by (induction xs) auto


subsection \<open>Removing Vertices from Lists\<close>
definition remove_vertices_list :: "'a list \<Rightarrow> 'a set \<Rightarrow> 'a list" (infix "\<setminus>" 60) where
  "\<sigma> \<setminus> X \<equiv> [v <- \<sigma>. v \<notin> X]"

lemma remove_vertices_not_in_list:
  "v \<in> X \<Longrightarrow> v \<notin> set (\<sigma> \<setminus> X)"
  unfolding remove_vertices_list_def
  by simp

lemma remove_vertices_list_disjoint: "X \<inter> set \<sigma> = {} \<Longrightarrow> \<sigma> \<setminus> X = \<sigma>"
  unfolding remove_vertices_list_def
  by (auto intro: filter_True)

lemma remove_vertex_not_in_list: "x \<notin> set \<sigma> \<Longrightarrow> \<sigma> \<setminus> {x} = \<sigma>"
  by (auto intro: remove_vertices_list_disjoint)

lemma length_at_least_two_Cons_Cons: "2 \<le> length xs \<Longrightarrow> \<exists>x x' xs'. xs = x # x' # xs'"
  by (metis Suc_le_length_iff numeral_2_eq_2)

subsection \<open>Moving a vertex to a position\<close>
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

definition move_to :: "'a list \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a list" ("_[_ \<mapsto> _]" [100,100]) where 
  "move_to xs v i \<equiv> (take i [x <- xs. x \<noteq> v]) @ v # (drop i [x <- xs. x \<noteq> v])"

lemma induct_list_nat[case_names nil_zero nil_suc cons_zero cons_suc]:
  assumes "P [] 0"
  assumes "\<And>n. P [] n \<Longrightarrow> P [] (Suc n)"
  assumes "\<And>x xs. P xs 0 \<Longrightarrow> P (x#xs) 0" 
  assumes "\<And>x xs n. P xs n \<Longrightarrow> P (x#xs) (Suc n)"
  shows "P xs n"
  using assms
  by (induction_schema) (pat_completeness, lexicographic_order)

lemma append_cong: "xs = xs' \<Longrightarrow> ys = ys' \<Longrightarrow> xs @ ys = xs' @ ys'"
  by simp

lemma move_to_gt_length:
  "length xs \<le> i \<Longrightarrow> xs[v \<mapsto> i] = xs[v \<mapsto> length xs]"
  unfolding move_to_def
  by (auto intro!: append_cong dest: le_trans[OF length_filter_le])

lemma move_to_Cons_Suc:
  assumes "x \<noteq> v"
  assumes "Suc n = i"
  shows "(x#xs)[v \<mapsto> i] = x # xs[v \<mapsto> n]"
  using assms
  unfolding move_to_def
  by auto

lemma move_hd_to:
  "(v#xs)[v \<mapsto> i] = xs[v \<mapsto> i]"
  unfolding move_to_def
  by auto

lemma move_to_neq_0_Cons:
  assumes "x \<noteq> v"
  assumes "i \<noteq> 0"
  shows "(x#xs)[v \<mapsto> i] = x # xs[v \<mapsto> (i - 1)]"
  using assms
  unfolding move_to_def
  by (auto simp: drop_Cons' take_Cons')

lemma move_to_0:
  shows "xs[v \<mapsto> 0] = v # [x <- xs. x \<noteq> v]"
  unfolding move_to_def
  by simp

lemma move_to_last:
  shows "xs[v \<mapsto> length xs] = [x <- xs. x \<noteq> v] @ [v]"
  unfolding move_to_def
  by simp

lemma move_to_Cons_eq:
  "(v#xs)[v \<mapsto> i] = xs[v \<mapsto> i]"
  unfolding move_to_def
  by simp

lemma move_to_distinct:
  "distinct xs \<Longrightarrow> distinct xs[x \<mapsto> i]"
  unfolding move_to_def
  by (auto dest: in_set_dropD in_set_takeD distinct_filter set_take_disj_set_drop_if_distinct)

lemma move_to_set: "set xs[x \<mapsto> i] = set xs \<union> {x}"
  unfolding move_to_def
  by (auto dest: in_set_takeD in_set_dropD)
     (metis (mono_tags, lifting) append_take_drop_id filter_set last_index_append last_index_size_conv length_append member_filter)

lemma move_to_insert_before:
  "i \<le> index \<sigma> w \<Longrightarrow> v \<noteq> w \<Longrightarrow> v \<notin> set \<sigma> \<Longrightarrow> index \<sigma>[v \<mapsto> i] w = Suc (index \<sigma> w)"
  by (induction \<sigma> i rule: induct_list_nat)
     (auto simp: move_to_0 move_to_Cons_Suc)

lemma move_to_insert_after:
  "index \<sigma> w < i \<Longrightarrow> i \<le> length \<sigma> \<Longrightarrow> v \<noteq> w \<Longrightarrow> v \<notin> set \<sigma> \<Longrightarrow> index \<sigma>[v \<mapsto> i] w = index \<sigma> w"
  by (induction \<sigma> i rule: induct_list_nat)
     (auto simp: move_to_Cons_Suc)


lemma index_less_filter_eq: "index xs w < index xs v \<Longrightarrow> index [x <- xs. x \<noteq> v] w = index xs w"
  by (induction xs) auto

lemma index_less_filter: "index xs w < index xs w' \<Longrightarrow> w \<noteq> v \<Longrightarrow> w' \<noteq> v \<Longrightarrow> index [x <- xs. x \<noteq> v] w < index [x <- xs. x \<noteq> v] w'"
  by (induction xs) auto

lemma not_in_take: "x \<notin> set xs \<Longrightarrow> x \<notin> set (take i xs)"
  by (auto dest: in_set_takeD)

lemma not_in_set_filter_length_eq: "v \<notin> set xs \<Longrightarrow> length [x <- xs. x \<noteq> v] = length xs"
  by (induction xs) auto

lemma in_set_distinct_filter_length_eq: "v \<in> set xs \<Longrightarrow> distinct xs \<Longrightarrow> length [x <- xs. x \<noteq> v] = length xs - 1"
  by (induction xs) (auto simp: not_in_set_filter_length_eq intro!: Suc_pred)

lemma distinct_filter_length: "distinct xs \<Longrightarrow> (length [x <- xs. x \<noteq> v] = length xs \<and> v \<notin> set xs) \<or> (length [x <- xs. x \<noteq> v] = length xs - 1 \<and> v \<in> set xs)"
  by (metis in_set_distinct_filter_length_eq not_in_set_filter_length_eq)


lemma filter_removeAll: "[x <- xs. x \<noteq> v] = removeAll v xs"
  by (induction xs) auto

lemma not_in_set_filter_id: "v \<notin> set xs \<Longrightarrow> [x <- xs. x \<noteq> v] = xs"
  by (simp add: filter_removeAll)

lemma count_zero: "count_list xs v = 0 \<Longrightarrow>  v \<notin> set xs"
  by (induction xs) (auto split: if_splits)

lemma count_in: "v \<in> set xs \<Longrightarrow> count_list xs v \<noteq> 0"
  by (induction xs) auto

lemma Suc_index_filter: "index xs v < index xs w \<Longrightarrow> v \<in> set xs \<Longrightarrow> count_list xs v = 1 \<Longrightarrow> Suc (index [x <- xs. x \<noteq> v] w) = index xs w"
  by (induction xs) (auto simp: not_in_set_filter_id[OF count_zero])

lemma not_Nil_length_SucE: "xs \<noteq> [] \<Longrightarrow> (\<And>n. length xs = Suc n \<Longrightarrow> P) \<Longrightarrow> P"
  by (induction xs) auto


lemma move_to_id:
  "count_list \<sigma> v = 1 \<Longrightarrow> \<sigma>[v \<mapsto> index \<sigma> v] = \<sigma>"
  by (induction \<sigma>) (auto simp: move_to_0 filter_id_conv move_to_Cons_Suc count_zero)

lemma move_to_front_less:
  assumes "i < index \<sigma> v"
  assumes "index \<sigma> w < i"
  shows "index \<sigma>[v \<mapsto> i] w = index \<sigma> w"
  using assms
  by (induction \<sigma> arbitrary: i)
     (auto split: if_splits elim: less_natE simp: move_to_Cons_Suc)

lemma move_to_front_between:
  assumes "count_list \<sigma> v \<le> 1"
  assumes "i < index \<sigma> v"
  assumes "i \<le> index \<sigma> w" "index \<sigma> w < index \<sigma> v"
  shows "index \<sigma>[v \<mapsto> i] w = Suc (index \<sigma> w)"
  using assms
  by (induction \<sigma> i rule: induct_list_nat)
     (auto split: if_splits simp: move_to_0 move_to_Cons_Suc)

lemma move_to_front_gr:
  assumes "count_list \<sigma> v = 1"
  assumes "i < index \<sigma> v" 
  assumes "index \<sigma> v < index \<sigma> w"
  shows "index \<sigma>[v \<mapsto> i] w = index \<sigma> w"
proof -
  have "v \<in> set \<sigma>"
    using assms count_notin by fastforce
  then have "count_list \<sigma> v = 1"
    using assms count_zero by blast

  with assms \<open>v \<in> set \<sigma>\<close> show ?thesis
    by (induction \<sigma> i rule: induct_list_nat)
       (auto split: if_splits simp: move_to_0 move_to_Cons_Suc Suc_index_filter)
qed

lemma move_to_back_less:
  assumes "index \<sigma> v < i"
  assumes "index \<sigma> w < index \<sigma> v"
  shows "index \<sigma>[v \<mapsto> i] w = index \<sigma> w"
  using assms
  by (induction \<sigma> arbitrary: i) (auto split: if_splits simp: move_to_neq_0_Cons)

lemma move_to_back_between:
  assumes "count_list \<sigma> v = 1"
  assumes "index \<sigma> v < i"  
  assumes "i < length \<sigma>"
  assumes "index \<sigma> v < index \<sigma> w" "index \<sigma> w \<le> i"
  shows "index \<sigma>[v \<mapsto> i] w + 1 = index \<sigma> w"
proof -
  have "v \<in> set \<sigma>"
    using assms count_notin by fastforce
  then have "count_list \<sigma> v = 1"
    using assms count_zero by blast
  with \<open>v \<in> set \<sigma>\<close> assms show ?thesis
    by (induction \<sigma> arbitrary: i)
       (auto simp: move_to_Cons_eq move_to_neq_0_Cons move_to_insert_after split: if_splits dest!: count_zero)
qed

lemma move_to_back_gr:
  assumes "count_list \<sigma> v = 1"
  assumes "index \<sigma> v < i" "i < length \<sigma>"
  assumes "i < index \<sigma> w"
  shows "index \<sigma>[v \<mapsto> i] w = index \<sigma> w"
  using assms
  by (induction \<sigma> i rule: induct_list_nat)
     (auto split: if_splits dest: count_zero
           simp: move_to_Cons_eq move_to_Cons_Suc move_to_insert_before)

lemma distinct_count_list_le: "distinct xs \<Longrightarrow> count_list xs x \<le> 1"
  by (induction xs) auto

lemma distinct_count_in_set: "distinct xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> count_list xs x = 1"
  by (induction xs) auto

lemma move_to_index_v:
  assumes "distinct \<sigma>"
  assumes "i < length \<sigma>"
  shows "index \<sigma>[v \<mapsto> i] v = i"
  using assms
proof (induction \<sigma> i rule: induct_list_nat)
  case (cons_suc x xs n)
  then show ?case 
    by (cases "x = v")
       (auto simp: move_to_Cons_Suc move_to_Cons_eq move_to_def index_append not_in_set_filter_id 
             dest: in_set_takeD split: if_splits)
qed (auto simp add: move_to_0)

lemma move_to_index_less:
  assumes "distinct \<sigma>"
  assumes "i < length \<sigma>"
  assumes "v \<noteq> w"
  assumes "index \<sigma> w < i"
  shows "index \<sigma>[v \<mapsto> i] w \<le> index \<sigma> w"
  using assms
proof (induction \<sigma> i rule: induct_list_nat)
  case (cons_suc x xs n)
  then show ?case 
    by (auto simp: move_to_Cons_Suc move_to_def index_append not_in_set_filter_id set_take_if_index
             dest: in_set_takeD index_take_if_set  split: if_splits)
qed auto

lemma move_to_front_decompE:
  assumes "distinct xs"
  assumes "xs = ps @ x # ss"
  assumes "i \<le> index xs x"
  obtains pps pss where "xs[x \<mapsto> i] = pps @ x # pss @ ss" "pps @ pss = ps"
  using assms
proof (induction xs i arbitrary: ps thesis rule: induct_list_nat)
  case (cons_zero a xs)
  then show ?case
    by (auto simp: move_to_0 not_in_set_filter_id) blast
next
  case (cons_suc a xs n)
  consider (eq) "a = x" | (neq) "a \<noteq> x" by blast
  then show ?case
  proof cases
    case eq
    with cons_suc.prems have "ps = []" 
      by (auto simp: Cons_eq_append_conv)
    with cons_suc show ?thesis 
      by (auto simp: move_to_0 not_in_set_filter_id)
  next
    case neq

    with cons_suc.prems obtain tl_ps where "ps = a # tl_ps" 
      by (auto simp: Cons_eq_append_conv)

    with cons_suc.prems have "xs = tl_ps @ x # ss" 
      by simp

    have "distinct xs"
      using cons_suc.prems(2) by simp

    have "n \<le> index xs x" 
      using cons_suc.prems(4) neq by auto

    with cons_suc.IH \<open>distinct xs\<close> \<open>xs = tl_ps @ x # ss\<close>
    obtain pps pss where "xs[x \<mapsto> n] = pps @ x # pss @ ss" "pps @ pss = tl_ps"
      by blast

    with cons_suc show ?thesis
      by (metis \<open>ps = a # tl_ps\<close> append_Cons move_to_Cons_Suc neq)
  qed
qed auto

lemma move_to_others_keep_order:
  assumes "v \<noteq> w" "v \<noteq> w'"
  assumes "index xs w < index xs w'"
  shows "index xs[v \<mapsto> i] w < index xs[v \<mapsto> i] w'"
  using assms
proof (induction xs arbitrary: i)
  case (Cons a xs)
  then show ?case
  proof (cases i)
    case 0
    with Cons show ?thesis
      by (auto simp: move_to_0 index_less_filter)
  next
    case (Suc nat)
    then show ?thesis
    proof (cases "a = v")
      case True
      with Cons show ?thesis
        by (auto simp: move_hd_to)
    next
      case False
      with Cons Suc show ?thesis
        by (auto split: if_splits simp: move_to_Cons_Suc index_less_filter)
    qed
  qed
qed simp

lemma index_less_index_leq_move_to:
  "index \<sigma> w < index \<sigma> v \<Longrightarrow> index \<sigma>[v \<mapsto> i] w \<le> index \<sigma> v"
  by (induction \<sigma> i rule: induct_list_nat)
     (auto split: if_splits simp: move_to_0 move_to_Cons_Suc)

end