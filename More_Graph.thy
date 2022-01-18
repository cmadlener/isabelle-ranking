theory More_Graph
  imports
    "AGF.Berge"
    "AGF.Bipartite"
begin

subsection \<open>Graphs\<close>
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

lemma graph_abs_edgeD: "graph_abs G \<Longrightarrow> {u,v} \<in> G \<Longrightarrow> u \<noteq> v"
  unfolding graph_abs_def by auto

subsection \<open>Matchings\<close>
lemma matching_empty[simp]: "matching {}"
  unfolding matching_def by simp


subsection \<open>Bipartite graphs\<close>
lemma partitioned_bipartite_empty[simp]: "partitioned_bipartite {} X"
  unfolding partitioned_bipartite_def by simp


lemma partitioned_bipartiteI:
  assumes "graph_abs E"
  assumes "\<And>e. e \<in> E \<Longrightarrow> \<exists>u v. e = {u,v} \<and> u \<in> X \<and> v \<in> Vs E - X"
  shows "partitioned_bipartite E X"
  using assms
  unfolding partitioned_bipartite_def
  by (auto simp: graph_abs_def)

lemma partitioned_bipartite_graph_absD:
  assumes "partitioned_bipartite E X"
  shows "graph_abs E"
  using assms
  unfolding partitioned_bipartite_def
  by (auto intro: graph_abs.intro)

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
  apply (intro partitioned_bipartiteI)
   apply (drule partitioned_bipartite_graph_absD)
  by (auto simp: vs_insert elim!: partitioned_bipartiteE intro: graph_abs_insert dest: partitioned_bipartite_graph_absD)

lemma partitioned_bipartite_union:
  assumes "partitioned_bipartite G X"
  assumes "partitioned_bipartite H X"
  shows "partitioned_bipartite (G \<union> H) X"
  using assms partitioned_bipartite_graph_absD
  by (auto intro!: partitioned_bipartiteI intro: graph_abs_union simp: vs_union)
     (meson DiffD1 DiffD2 partitioned_bipartiteE)+

lemma partitioned_bipartite_compr:
  assumes "u \<notin> X" "u \<notin> Y" "finite X" "X \<subseteq> Y"
  shows "partitioned_bipartite {{u,v} |v. v \<in> X} Y"
  using assms
  by (intro partitioned_bipartiteI)
     (auto simp: graph_abs_compr vs_compr)

lemma partitioned_bipartite_swap:
  assumes bipartite: "partitioned_bipartite G X"
      and vertices_subset: "Vs G \<subseteq> X \<union> Y"
      and disjoint: "X \<inter> Y = {}"
    shows "partitioned_bipartite G Y" 
  using assms
proof -
  from bipartite have "graph_abs G" by (auto dest: partitioned_bipartite_graph_absD)

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

  with \<open>graph_abs G\<close> show "partitioned_bipartite G Y" 
    by (auto intro: partitioned_bipartiteI)
qed



end