theory More_Graph
  imports
    "AGF.Berge"
begin

sledgehammer_params [provers = cvc4 vampire verit e spass z3 zipperposition]

type_synonym 'a graph = "'a set set"

subsection \<open>Graphs\<close>
lemma edge_commute: "{u,v} \<in> G \<Longrightarrow> {v,u} \<in> G"
  by (simp add: insert_commute)

lemma vs_empty[simp]: "Vs {} = {}"
  by (simp add: Vs_def)

lemma vs_insert: "Vs (insert e E) = e \<union> Vs E"
  unfolding Vs_def by simp

lemma vs_union: "Vs (A \<union> B) = Vs A \<union> Vs B"
  unfolding Vs_def by simp

lemma vs_compr: "Vs {{u, v} |v. v \<in> ns} = (if ns = {} then {} else {u} \<union> ns)"
  unfolding Vs_def by auto

lemma graph_abs_empty[simp]: "graph_abs {}"
  by (simp add: graph_abs_def)

lemma graph_abs_insert[simp]: "graph_abs M \<Longrightarrow> u \<noteq> v \<Longrightarrow> graph_abs (insert {u,v} M)"
  by (auto simp: graph_abs_def Vs_def)

lemma graph_abs_union: "graph_abs G \<Longrightarrow> graph_abs H \<Longrightarrow> graph_abs (G \<union> H)"
  by (auto simp: graph_abs_def Vs_def)

lemma graph_abs_compr: "u \<notin> ns \<Longrightarrow> finite ns \<Longrightarrow> graph_abs {{u, v} |v. v \<in> ns}"
  unfolding graph_abs_def by (auto simp: Vs_def)

lemma graph_abs_subgraph: "graph_abs G \<Longrightarrow> G' \<subseteq> G \<Longrightarrow> graph_abs G'"
  unfolding graph_abs_def by (auto dest: Vs_subset intro: finite_subset)

lemma graph_abs_edgeD: "graph_abs G \<Longrightarrow> {u,v} \<in> G \<Longrightarrow> u \<noteq> v"
  unfolding graph_abs_def by auto

lemma graph_abs_no_edge_no_vertex:
  "graph_abs G \<Longrightarrow> \<forall>v. {u,v} \<notin> G \<Longrightarrow> u \<notin> Vs G"
  unfolding graph_abs_def Vs_def
  by (auto simp: insert_commute)

lemma graph_abs_vertex_edgeE:
  assumes "graph_abs G"
  assumes "v \<in> Vs G"
  obtains u where "{u,v} \<in> G"
  using assms
  by (meson edge_commute graph_abs_no_edge_no_vertex)

lemma symm_diff_empty[simp]:
  "G = G' \<Longrightarrow> G \<oplus> G' = {}"
  unfolding symmetric_diff_def
  by simp

lemma sym_diff_sym:
  "s \<oplus> s' = s' \<oplus> s"
  unfolding symmetric_diff_def
  by blast

lemma alt_path_sym_diff_rev_alt_path:
  assumes "graph_abs M" "graph_abs M'"
  assumes "M \<oplus> M' = set (edges_of_path p)"
  assumes "alt_path M p"
  shows "rev_alt_path M' p"
  using assms
  by (smt (verit, ccfv_SIG) UnE alt_list_cong subsetD sym_diff_subset symm_diff_mutex)

lemma rev_alt_path_sym_diff_alt_path:
  assumes "graph_abs M" "graph_abs M'"
  assumes "M \<oplus> M' = set (edges_of_path p)"
  assumes "rev_alt_path M p"
  shows "alt_path M' p"
  using assms
  by (smt (verit, ccfv_SIG) UnE alt_list_cong subsetD sym_diff_subset symm_diff_mutex)

lemma alt_list_distinct:
  assumes "alt_list P Q xs"
  assumes "distinct [x <- xs. P x]"
  assumes "distinct [x <- xs. Q x]"
  assumes "\<forall>x. \<not>(P x \<and> Q x)"
  shows "distinct xs"
  using assms
  by (induction xs rule: induct_alt_list012)
     (auto split: if_splits)


subsection \<open>Matchings\<close>
lemma matching_empty[simp]: "matching {}"
  unfolding matching_def by simp

lemma matching_subgraph: "matching M \<Longrightarrow> M' \<subseteq> M \<Longrightarrow> matching M'"
  unfolding matching_def
  by auto

lemma the_match: "matching M \<Longrightarrow> {u,v} \<in> M \<Longrightarrow> (THE u. {u,v} \<in> M) = u"
  apply (auto intro!: the_equality )
  by (metis doubleton_eq_iff insertI1 matching_unique_match)

lemma the_match': "matching M \<Longrightarrow> {u,v} \<in> M \<Longrightarrow> (THE v. {u,v} \<in> M) = v"
  apply (auto intro!: the_equality)
  by (metis (mono_tags, lifting) insert_commute the_match)

lemma the_match'': "matching M \<Longrightarrow> {u,v} \<in> M \<Longrightarrow> (THE u. {v,u} \<in> M) = u"
  by (auto dest: the_match edge_commute)

lemma the_match''': "matching M \<Longrightarrow> {u,v} \<in> M \<Longrightarrow> (THE v. {v,u} \<in> M) = v"
  by (auto dest: the_match' edge_commute)


definition maximal_matching :: "'a graph \<Rightarrow> 'a graph \<Rightarrow> bool" where
  "maximal_matching G M \<equiv> matching M \<and> (\<forall>u v. {u,v} \<in> G \<longrightarrow> u \<in> Vs M \<or> v \<in> Vs M)"

lemma maximal_matchingI:
  assumes "matching M"
  assumes "\<And>u v. {u,v} \<in> G \<Longrightarrow> u \<in> Vs M \<or> v \<in> Vs M"
  shows "maximal_matching G M"
  using assms
  unfolding maximal_matching_def
  by auto

lemma maximal_matching_edgeE:
  assumes "maximal_matching G M"
  assumes "{u,v} \<in> G"
  obtains e where "e \<in> M" "u \<in> e \<or> v \<in> e"
  using assms
  unfolding maximal_matching_def
  by (meson vs_member)

lemma maximal_matchingD:
  assumes "maximal_matching G M"
  shows "matching M"
  using assms
  unfolding maximal_matching_def
  by auto

lemma maximal_matching_edgeD:
  assumes "maximal_matching G M"
  assumes "{u,v} \<in> G"
  shows "u \<in> Vs M \<or> v \<in> Vs M"
  using assms
  by (auto elim: maximal_matching_edgeE)

lemma not_maximal_matchingE:
  assumes "matching M"
  assumes "\<not>maximal_matching G M"
  obtains u v where "{u,v} \<in> G" "u \<notin> Vs M" "v \<notin> Vs M"
  using assms
  unfolding maximal_matching_def graph_abs_def
  by auto


subsection \<open>Bipartite graphs\<close>
definition bipartite :: "'a graph \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "bipartite G X Y \<equiv> X \<inter> Y = {} \<and> (\<forall>e \<in> G. \<exists>u v. e = {u,v} \<and> u \<in> X \<and> v \<in> Y)"

lemma bipartiteI:
  assumes "X \<inter> Y = {}"
  assumes "\<And>e. e \<in> G \<Longrightarrow> \<exists>u v. e = {u,v} \<and> u \<in> X \<and> v \<in> Y"
  shows "bipartite G X Y"
  using assms
  unfolding bipartite_def
  by auto

lemma bipartite_disjointD:
  assumes "bipartite G X Y"
  shows "X \<inter> Y = {}"
  using assms
  unfolding bipartite_def
  by blast

lemma bipartite_edgeE:
  assumes "e \<in> G"
  assumes "bipartite G X Y"
  obtains x y where "x \<in> X" "y \<in> Y" "e = {x,y}" "x \<noteq> y"
  using assms
  unfolding bipartite_def
  by fast

lemma bipartite_edgeD:
  assumes "{u,v} \<in> G"
  assumes "bipartite G X Y"
  shows
    "u \<in> X \<Longrightarrow> v \<in> Y - X"
    "u \<in> Y \<Longrightarrow> v \<in> X - Y"
    "v \<in> X \<Longrightarrow> u \<in> Y - X"
    "v \<in> Y \<Longrightarrow> u \<in> X - Y"
  using assms
  unfolding bipartite_def
  by fast+

lemma bipartite_empty[simp]: "X \<inter> Y = {} \<Longrightarrow> bipartite {} X Y"
  unfolding bipartite_def by blast

lemma bipartite_empty_part_iff_empty: "bipartite G {} Y \<longleftrightarrow> G = {}"
  unfolding bipartite_def by blast

lemma bipartite_commute:
  "bipartite G X Y \<Longrightarrow> bipartite G Y X"
  unfolding bipartite_def
  by fast

lemma bipartite_subgraph:
  "bipartite G X Y \<Longrightarrow> G' \<subseteq> G \<Longrightarrow> bipartite G' X Y"
  unfolding bipartite_def
  by blast

lemma bipartite_vs_subset: "bipartite G X Y \<Longrightarrow> Vs G \<subseteq> X \<union> Y"
  unfolding bipartite_def Vs_def
  by auto

lemma finite_bipartite_graph_abs:
  "finite X \<Longrightarrow> finite Y \<Longrightarrow> bipartite G X Y \<Longrightarrow> graph_abs G"
  unfolding graph_abs_def
  by (auto dest: bipartite_vs_subset intro: finite_subset elim!: bipartite_edgeE)

lemma bipartite_insertI:
  assumes "bipartite G X Y"
  assumes "u \<in> X" "v \<in> Y"
  shows "bipartite (insert {u,v} G) X Y"
  using assms
  unfolding bipartite_def
  by auto

lemma bipartite_unionI:
  assumes "bipartite G X Y"
  assumes "bipartite H X Y"
  shows "bipartite (G \<union> H) X Y"
  using assms
  unfolding bipartite_def
  by auto

lemma bipartite_reduced_to_vs:
  "bipartite G X Y \<Longrightarrow> bipartite G (X \<inter> Vs G) (Y \<inter> Vs G)"
  unfolding bipartite_def
  by auto (metis edges_are_Vs)

subsection \<open>Removing Vertices from Graphs\<close>
definition remove_vertices_graph :: "'a graph \<Rightarrow> 'a set \<Rightarrow> 'a graph" (infixl "\<setminus>" 60) where
  "G \<setminus> X \<equiv> {e. e \<in> G \<and> e \<inter> X = {}}"

lemma remove_vertices_empty:
  "G \<setminus> {} = G"
  unfolding remove_vertices_graph_def by simp

lemma remove_vertices_not_vs:
  "v \<in> X \<Longrightarrow> v \<notin> Vs (G \<setminus> X)"
  unfolding Vs_def remove_vertices_graph_def by blast

lemma remove_vertices_not_vs':
  "v \<in> X \<Longrightarrow> v \<in> Vs (G \<setminus> X) \<Longrightarrow> False"
  using remove_vertices_not_vs by force

lemma remove_vertices_subgraph:
  "G \<setminus> X \<subseteq> G"
  unfolding remove_vertices_graph_def
  by simp

lemma remove_vertices_subgraph':
  "e \<in> G \<setminus> X \<Longrightarrow> e \<in> G"
  using remove_vertices_subgraph 
  by fast

lemma remove_vertices_subgraph_Vs:
  "v \<in> Vs (G \<setminus> X) \<Longrightarrow> v \<in> Vs G" 
  using Vs_subset[OF remove_vertices_subgraph]
  by fast

lemma in_remove_verticesI:
  "e \<in> G \<Longrightarrow> e \<inter> X = {} \<Longrightarrow> e \<in> G \<setminus> X"
  unfolding remove_vertices_graph_def
  by blast

lemma in_remove_vertices_subsetI:
  "X' \<subseteq> X \<Longrightarrow> e \<in> G \<setminus> X' \<Longrightarrow> e \<inter> X - X' = {} \<Longrightarrow> e \<in> G \<setminus> X"
  unfolding remove_vertices_graph_def
  by blast

lemma in_remove_vertices_vsI:
  "e \<in> G \<Longrightarrow> e \<inter> X = {} \<Longrightarrow> u \<in> e \<Longrightarrow> u \<in> Vs (G \<setminus> X)"
  by (auto dest: in_remove_verticesI)

lemma remove_vertices_only_vs:
  "G \<setminus> X = G \<setminus> (X \<inter> Vs G)"
  unfolding remove_vertices_graph_def Vs_def
  by blast

lemma remove_vertices_mono:
  "G' \<subseteq> G \<Longrightarrow> e \<in> G' \<setminus> X \<Longrightarrow> e \<in> G \<setminus> X"
  unfolding remove_vertices_graph_def by blast

lemma remove_vertices_inv_mono:
  "X \<subseteq> X' \<Longrightarrow> e \<in> G \<setminus> X' \<Longrightarrow> e \<in> G \<setminus> X"
  unfolding remove_vertices_graph_def by blast

lemma remove_vertices_inv_mono':
  "X \<subseteq> X' \<Longrightarrow> G \<setminus> X' \<subseteq> G \<setminus> X"
  by (auto dest: remove_vertices_inv_mono)

lemma remove_vertices_graph_disjoint: "X \<inter> Vs G = {} \<Longrightarrow> G \<setminus> X = G"
  unfolding Vs_def remove_vertices_graph_def by blast

lemma remove_vertex_not_in_graph: "x \<notin> Vs G \<Longrightarrow> G \<setminus> {x} = G"
  by (auto intro!: remove_vertices_graph_disjoint)



lemma graph_abs_remove_vertices:
  "graph_abs G \<Longrightarrow> graph_abs (G \<setminus> X)"
  by (simp add: graph_abs_subgraph remove_vertices_graph_def)

lemma bipartite_remove_vertices:
  "bipartite G U V \<Longrightarrow> bipartite (G \<setminus> X) U V"
  using remove_vertices_subgraph
  by (auto intro: bipartite_subgraph)

lemma matching_remove_vertices:
  "matching M \<Longrightarrow> matching (M \<setminus> X)"
  using remove_vertices_subgraph
  by (auto intro: matching_subgraph)


lemma remove_remove_union: "G \<setminus> X \<setminus> Y = G \<setminus> X \<union> Y"
  unfolding remove_vertices_graph_def by blast


lemma remove_edge_matching: "matching M \<Longrightarrow> {u,v} \<in> M \<Longrightarrow> M \<setminus> {u,v} = M - {{u,v}}"
  unfolding remove_vertices_graph_def
  by auto (metis empty_iff insert_iff matching_unique_match)+

lemma remove_vertex_matching: "matching M \<Longrightarrow> {u,v} \<in> M \<Longrightarrow> M \<setminus> {u} = M - {{u,v}}"
  unfolding remove_vertices_graph_def
  by auto (metis empty_iff insert_iff matching_unique_match)+

lemma remove_vertex_matching': "matching M \<Longrightarrow> {u,v} \<in> M \<Longrightarrow> M \<setminus> {v} = M - {{u,v}}"
  unfolding remove_vertices_graph_def
  by auto (metis empty_iff insert_iff matching_unique_match)+


lemma remove_edge_matching_vs: "matching M \<Longrightarrow> {u,v} \<in> M \<Longrightarrow> Vs (M \<setminus> {u,v}) = Vs M - {u,v}"
  by (auto simp add: remove_edge_matching Vs_def) (metis empty_iff insert_iff matching_unique_match)+

lemma remove_vertex_matching_vs: "matching M \<Longrightarrow> {u,v} \<in> M \<Longrightarrow> Vs (M \<setminus> {u}) = Vs M - {u,v}"
  by (metis remove_edge_matching remove_edge_matching_vs remove_vertex_matching)

lemma remove_vertex_matching_vs': "matching M \<Longrightarrow> {u,v} \<in> M \<Longrightarrow> Vs (M \<setminus> {v}) = Vs M - {u,v}"
  by (metis remove_edge_matching remove_edge_matching_vs remove_vertex_matching')

lemma remove_vertices_in_diff: "{u,v} \<in> G \<setminus> X \<Longrightarrow> {u,v} \<notin> G \<setminus> X' \<Longrightarrow> u \<in> X' - X \<or> v \<in> X' - X"
  unfolding remove_vertices_graph_def
  by simp

end