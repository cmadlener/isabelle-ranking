theory More_Graph
  imports
    "AGF.Berge"
    "AGF.Bipartite"
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


subsection \<open>Matchings\<close>
lemma matching_empty[simp]: "matching {}"
  unfolding matching_def by simp

lemma matching_subgraph: "matching M \<Longrightarrow> M' \<subseteq> M \<Longrightarrow> matching M'"
  unfolding matching_def
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
  by auto (metis edges_are_Vs insert_commute)

lemma partitioned_bipartite_empty[simp]: "partitioned_bipartite {} X"
  unfolding partitioned_bipartite_def by simp


lemma partitioned_bipartiteI:
  assumes "finite E"
  assumes "\<And>e. e \<in> E \<Longrightarrow> \<exists>u v. e = {u,v} \<and> u \<in> X \<and> v \<in> Vs E - X"
  shows "partitioned_bipartite E X"
  using assms
  unfolding partitioned_bipartite_def
  by auto

lemma partitioned_bipartite_graph_absD:
  assumes "partitioned_bipartite E X"
  shows "graph_abs E"
  using assms
  by (auto dest: partitioned_bipartite_graph_invar intro: graph_abs.intro)

lemma partitioned_bipartite_finiteD:
  assumes "partitioned_bipartite E X"
  shows "finite E"
  using assms
  unfolding partitioned_bipartite_def by blast

lemma partitioned_bipartiteE:
  assumes "partitioned_bipartite E X"
  assumes "e \<in> E"
  obtains u v where "e = {u,v}" "u \<in> X" "v \<in> Vs E - X"
  using assms
  unfolding partitioned_bipartite_def
  by fast

lemma partitioned_bipartite_insertI:
  assumes "partitioned_bipartite E X"
  assumes "u \<notin> X" "v \<in> X"
  shows "partitioned_bipartite (insert {u,v} E) X"
  using assms
  apply (auto intro!: partitioned_bipartiteI dest: partitioned_bipartite_finiteD 
              simp: partitioned_bipartite_def vs_insert)
  by meson

lemma partitioned_bipartite_union:
  assumes "partitioned_bipartite G X"
  assumes "partitioned_bipartite H X"
  shows "partitioned_bipartite (G \<union> H) X"
  using assms
  apply (auto intro!: partitioned_bipartiteI intro: graph_abs_union simp: vs_union partitioned_bipartite_def
              dest: partitioned_bipartite_finiteD)
  by meson+

lemma partitioned_bipartite_compr:
  assumes "u \<notin> X" "u \<notin> Y" "finite X" "X \<subseteq> Y"
  shows "partitioned_bipartite {{u,v} |v. v \<in> X} Y"
  using assms
  by (intro partitioned_bipartiteI)
     (auto simp: graph_abs_compr vs_compr)

lemma partitioned_bipartite_subgraph:
  assumes "partitioned_bipartite G X"
  assumes "G' \<subseteq> G"
  shows "partitioned_bipartite G' X"
  using assms
  unfolding partitioned_bipartite_def
  apply (auto simp: finite_subset)
  by (metis insertI1 subsetD subset_insertI vs_member_intro)

lemma partitioned_bipartite_swap:
  assumes bipartite: "partitioned_bipartite G X"
      and vertices_subset: "Vs G \<subseteq> X \<union> Y"
      and disjoint: "X \<inter> Y = {}"
    shows "partitioned_bipartite G Y" 
  using assms
proof -
  have "finite G" using bipartite by (auto dest: partitioned_bipartite_finiteD)

  {
    fix e
    assume "e \<in> G"
    then obtain u v where "e = {u,v}" "u \<in> X" "v \<in> Vs G - X"
      using bipartite
      by (auto elim: partitioned_bipartiteE)

    then have "u \<in> Vs G - Y" 
      using vertices_subset disjoint
      by (metis DiffI \<open>e \<in> G\<close> disjoint_iff_not_equal insertI1 vs_member)

    then have "v \<in> Y" using vertices_subset \<open>v \<in> Vs G - X\<close> by fastforce

    with \<open>e = {u,v}\<close> \<open>u \<in> Vs G - Y\<close> have "\<exists>u v. e = {u,v} \<and> u \<in> Y \<and> v \<in> Vs G - Y"
      by blast
  }

  with \<open>finite G\<close> show "partitioned_bipartite G Y" 
    by (auto intro: partitioned_bipartiteI)
qed



end