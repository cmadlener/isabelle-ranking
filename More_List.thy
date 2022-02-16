theory More_List
  imports "List-Index.List_Index"
begin

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


end