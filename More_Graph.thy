theory More_Graph
  imports
    "AGF.Berge"
begin

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

lemma symm_diff_empty[simp]:
  "G = G' \<Longrightarrow> G \<oplus> G' = {}"
  unfolding symmetric_diff_def
  by simp

lemma sym_diff_sym:
  "s \<oplus> s' = s' \<oplus> s"
  unfolding symmetric_diff_def
  by blast

subsection \<open>Matchings\<close>
lemma matching_empty[simp]: "matching {}"
  unfolding matching_def by simp

lemma matching_subgraph: "matching M \<Longrightarrow> M' \<subseteq> M \<Longrightarrow> matching M'"
  unfolding matching_def
  by auto

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


end