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
  assumes "u \<in> Vs G"
  obtains v where "{u,v} \<in> G"
  using assms
  by (meson graph_abs_no_edge_no_vertex)

lemma graph_abs_vertex_edgeE':
  assumes "graph_abs G"
  assumes "v \<in> Vs G"
  obtains u where "{u,v} \<in> G"
  using assms
  by (auto elim: graph_abs_vertex_edgeE dest: edge_commute)

lemma graph_abs_edges_of_distinct_path:
  "distinct p \<Longrightarrow> graph_abs (set (edges_of_path p))"
  by (induction p rule: edges_of_path.induct) auto

lemma vs_neq_graphs_neq:
  "x \<in> Vs G \<Longrightarrow> x \<notin> Vs H \<Longrightarrow> G \<noteq> H"
  by blast

lemma path_Cons_hd:
  "path G vs \<Longrightarrow> hd vs = v \<Longrightarrow> {u,v} \<in> G \<Longrightarrow> path G (u#vs)"
  by (cases vs) auto

lemma symm_diff_empty[simp]:
  "G = G' \<Longrightarrow> G \<oplus> G' = {}"
  unfolding symmetric_diff_def
  by simp

lemma sym_diff_sym:
  "s \<oplus> s' = s' \<oplus> s"
  unfolding symmetric_diff_def
  by blast

lemma alt_path_sym_diff_rev_alt_path:
  assumes "M \<oplus> M' = set (edges_of_path p)"
  assumes "alt_path M p"
  shows "rev_alt_path M' p"
  using assms
  by (auto intro: alt_list_cong simp: symmetric_diff_def)

lemma rev_alt_path_sym_diff_alt_path:
  assumes "M \<oplus> M' = set (edges_of_path p)"
  assumes "rev_alt_path M p"
  shows "alt_path M' p"
  using assms
  by (auto intro: alt_list_cong simp: symmetric_diff_def)

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
  by (auto intro!: the_equality)
     (metis doubleton_eq_iff insertI1 matching_unique_match)

lemma the_match': "matching M \<Longrightarrow> {u,v} \<in> M \<Longrightarrow> (THE v. {u,v} \<in> M) = v"
  by (auto dest: the_match edge_commute)

lemma the_match'': "matching M \<Longrightarrow> {u,v} \<in> M \<Longrightarrow> (THE u. {v,u} \<in> M) = u"
  by (auto dest: the_match edge_commute)

lemma the_match''': "matching M \<Longrightarrow> {u,v} \<in> M \<Longrightarrow> (THE v. {v,u} \<in> M) = v"
  by (auto dest: the_match' edge_commute)

lemma matching_card_vs:
  assumes "graph_abs M"
  assumes "matching M"
  shows "2 * card M = card (Vs M)"
  using assms
  by (auto simp:  Vs_def card_2_iff card_partition graph_abs.finite_E graph_abs_def matching_def)

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
  by (auto simp: vs_member)

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

lemma remove_vertex_psubset: "x \<in> Vs G \<Longrightarrow> x \<in> X \<Longrightarrow> G \<setminus> X < G"
  by (auto intro: remove_vertices_subgraph' dest: remove_vertices_not_vs vs_neq_graphs_neq)

lemma remove_vertex_card_less: "finite G \<Longrightarrow> x \<in> Vs G \<Longrightarrow> x \<in> X \<Longrightarrow> card (G \<setminus> X) < card G"
  by (auto intro: psubset_card_mono intro!: remove_vertex_psubset)



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

lemma finite_remove_vertices:
  "finite G \<Longrightarrow> finite (G \<setminus> X)"
  by (auto intro: finite_subset[OF remove_vertices_subgraph])


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


lemma maximal_matching_remove_edges:
  assumes "M \<subseteq> G"
  assumes "E \<subseteq> M"
  assumes "X = Vs E"
  assumes "maximal_matching G M"
  shows "maximal_matching (G \<setminus> X) (M \<setminus> X)"
  unfolding maximal_matching_def
proof (intro conjI allI impI)
  show "matching (M \<setminus> X)" using assms
    by (auto simp: maximal_matching_def intro: matching_remove_vertices)
next
  fix u v
  assume "{u,v} \<in> G \<setminus> X"

  then have "{u,v} \<in> G" "u \<notin> X" "v \<notin> X"
    by (auto dest: remove_vertices_subgraph' remove_vertices_not_vs edges_are_Vs)

  with \<open>maximal_matching G M\<close> consider "u \<in> Vs M" | "v \<in> Vs M"
    by (auto dest: maximal_matching_edgeD)

  then show "u \<in> Vs (M \<setminus> X) \<or> v \<in> Vs (M \<setminus> X)"
  proof cases
    case 1
    then obtain e where "e \<in> M" "u \<in> e"
      by (auto simp: vs_member)

    with assms \<open>u \<notin> X\<close> have "e \<in> M \<setminus> X"
      apply (auto intro!: in_remove_verticesI)
      by (smt (verit, del_insts) matching_unique_match maximal_matching_def subset_iff vs_member)

    with \<open>u \<in> e\<close> show ?thesis
      by blast
  next
    case 2
    then obtain e where "e \<in> M" "v \<in> e"
      by (auto simp: vs_member)

    with assms \<open>v \<notin> X\<close> have "e \<in> M \<setminus> X"
      apply (auto intro!: in_remove_verticesI)
      by (smt (verit, del_insts) matching_unique_match maximal_matching_def subset_iff vs_member)

    with \<open>v \<in> e\<close> show ?thesis
      by blast
  qed
qed

definition max_card_matching :: "'a graph \<Rightarrow> 'a graph \<Rightarrow> bool" where
  "max_card_matching G M \<longleftrightarrow> M \<subseteq> G \<and> matching M \<and> (\<forall>M'. M' \<subseteq> G \<and> matching M' \<longrightarrow> card M' \<le> card M)"

definition perfect_matching :: "'a graph \<Rightarrow> 'a graph \<Rightarrow> bool" where
  "perfect_matching G M \<longleftrightarrow> M \<subseteq> G \<and> matching M \<and> Vs G = Vs M"

lemma max_card_matchingI:
  assumes "M \<subseteq> G" "matching M"
  assumes "\<And>M'. M' \<subseteq> G \<Longrightarrow> matching M' \<Longrightarrow> card M' \<le> card M"
  shows "max_card_matching G M"
  using assms
  unfolding max_card_matching_def
  by blast

lemma max_card_matchingD:
  assumes "max_card_matching G M"
  shows "M \<subseteq> G \<and> matching M \<and> (\<forall>M'. M' \<subseteq> G \<and> matching M' \<longrightarrow> card M' \<le> card M)"
  using assms
  unfolding max_card_matching_def
  by blast

lemma max_card_matching_ex:
  assumes "finite G"
  shows "\<exists>M. max_card_matching G M"
proof (rule ccontr)
  assume no_max_card: "\<nexists>M. max_card_matching G M"

  obtain M where "M \<subseteq> G" "matching M"
    using matching_empty by blast

  then show False
  proof (induction "card G - card M" arbitrary: M rule: less_induct)
    case less
    with no_max_card obtain M' where "M' \<subseteq> G" "matching M'" "card M < card M'"
      unfolding max_card_matching_def
      by auto

    with less assms show ?case
      by (metis card_mono diff_less_mono2 leD psubsetI psubset_card_mono)
  qed
qed

lemma max_card_matchings_same_size:
  assumes "max_card_matching G M"
  assumes "max_card_matching G M'"
  shows "card M = card M'"
  using assms
  unfolding max_card_matching_def
  by (simp add: dual_order.eq_iff)

lemma max_card_matching_cardI:
  assumes "max_card_matching G M"
  assumes "card M = card M'"
  assumes "M' \<subseteq> G" "matching M'"
  shows "max_card_matching G M'"
  using assms
  unfolding max_card_matching_def
  by simp

lemma perfect_matchingI:
  assumes "M \<subseteq> G" "matching M" "Vs G = Vs M"
  shows "perfect_matching G M"
  using assms
  unfolding perfect_matching_def
  by blast

lemma perfect_matching_max_card_matchingI:
  assumes "max_card_matching G M"
  assumes "Vs G = Vs M"
  shows "perfect_matching G M"
  using assms
  unfolding max_card_matching_def
  by (auto intro: perfect_matchingI)

lemma perfect_matchingD:
  assumes "perfect_matching G M"
  shows "M \<subseteq> G" "matching M" "Vs G = Vs M"
  using assms
  unfolding perfect_matching_def
  by blast+

lemma perfect_matching_is_max_card_matching: 
  assumes "graph_abs G"
  assumes perfect: "perfect_matching G M"
  shows "max_card_matching G M"
proof (rule ccontr)
  assume not_max_card: "\<not>max_card_matching G M"

  from perfect have "M \<subseteq> G" "matching M" "Vs G = Vs M"
    by (auto dest: perfect_matchingD)

  with not_max_card obtain M' where bigger_matching: "M' \<subseteq> G" "matching M'" "card M < card M'"
    unfolding max_card_matching_def perfect_matching_def
    by auto

  from bigger_matching have *: "2 * card M < 2 * card M'"
    by linarith

  from \<open>graph_abs G\<close> \<open>M \<subseteq> G\<close> \<open>M' \<subseteq> G\<close> have "graph_abs M" "graph_abs M'"
    by (auto intro: graph_abs_subgraph)

  with * \<open>matching M\<close> \<open>matching M'\<close> have "card (Vs M) < card (Vs M')"
    by (auto simp: matching_card_vs)

  with \<open>Vs G = Vs M\<close>[symmetric] \<open>M' \<subseteq> G\<close> \<open>graph_abs G\<close> show False
    by (auto simp: Vs_def Union_mono card_mono leD dest: graph_abs.graph)
qed

lemma max_card_matching_remove_vertices:
  assumes "max_card_matching G M"
  assumes "X \<subseteq> Vs G - Vs M"
  shows "max_card_matching (G \<setminus> X) M"
proof (rule ccontr)
  assume contr: "\<not>max_card_matching (G \<setminus> X) M"

  from assms have "M \<subseteq> G \<setminus> X"
    by (auto dest: max_card_matchingD intro: in_remove_verticesI)

  with assms contr obtain M' where M': "M' \<subseteq> G \<setminus> X" "matching M'" "card M' > card M"
    by (auto simp: max_card_matching_def)

  then have "M' \<subseteq> G"
    by (auto intro: remove_vertices_subgraph')

  with M' assms show False
    by (simp add: leD max_card_matchingD)
qed

function make_perfect_matching :: "'a graph \<Rightarrow> 'a graph \<Rightarrow> 'a graph" where
  "make_perfect_matching G M = (
    if (\<exists>x. x \<in> Vs G \<and> x \<notin> Vs M)
    then make_perfect_matching (G \<setminus> {SOME x. x \<in> Vs G \<and> x \<notin> Vs M}) M
    else G
  )
  " if "finite G"
| "make_perfect_matching G M = G" if "infinite G"
  by auto

termination
  by (relation "measure (card \<circ> fst)")
     (auto intro: remove_vertex_card_less dest!: someI_ex)

lemma subgraph_vs_subset_eq:
  assumes "M \<subseteq> G"
  assumes "Vs G \<subseteq> Vs M"
  shows "Vs G = Vs M"
  using assms
  unfolding Vs_def
  by auto

lemma subgraph_remove_some_ex:
  "\<exists>x. x \<in> Vs G \<and> x \<notin> Vs M \<Longrightarrow> M \<subseteq> G \<Longrightarrow> M \<subseteq> G \<setminus> {SOME x. x \<in> Vs G \<and> x \<notin> Vs M}"
    by (auto intro: in_remove_verticesI dest!: someI_ex)

lemma max_card_matching_make_perfect_matching:
  assumes "matching M" "M \<subseteq> G" "graph_abs G" "finite G"
  shows "max_card_matching (make_perfect_matching G M) M"
  using assms
proof (induction G M rule: make_perfect_matching.induct)
  case (1 G M)
  show ?case
  proof (cases "\<exists>x. x \<in> Vs G \<and> x \<notin> Vs M")
    case True
    with \<open>M \<subseteq> G\<close> have "M \<subseteq> G \<setminus> {SOME x. x \<in> Vs G \<and> x \<notin> Vs M}"
      by (intro subgraph_remove_some_ex)

    from "1.IH"[OF True \<open>matching M\<close> this graph_abs_remove_vertices[OF \<open>graph_abs G\<close>] finite_remove_vertices[OF \<open>finite G\<close>]] True \<open>finite G\<close>
    show ?thesis
      by simp
  next
    case False
    with 1 have "perfect_matching G M"
      by (auto intro!: perfect_matchingI subgraph_vs_subset_eq)
    
    with 1 False show ?thesis
      by (auto dest: perfect_matching_is_max_card_matching)
  qed
qed simp

lemma vs_make_perfect_matching:
  assumes "M \<subseteq> G"
  assumes "finite G"
  shows "Vs (make_perfect_matching G M) = Vs M"
  using assms
proof (induction G M rule: make_perfect_matching.induct)
  case (1 G M)
  show ?case
  proof (cases "\<exists>x. x \<in> Vs G \<and> x \<notin> Vs M")
    case True

    from \<open>finite G\<close> True 1 show ?thesis
      by simp (intro "1.IH" finite_remove_vertices subgraph_remove_some_ex)
  next
    case False
    with 1 show ?thesis
      by (auto dest: Vs_subset)
  qed
qed blast

lemma perfect_matching_make_perfect_matching:
  assumes "finite G" "graph_abs G"
  assumes "matching M" "M \<subseteq> G"
  shows "perfect_matching (make_perfect_matching G M) M"
  using assms
  by (auto simp del: make_perfect_matching.simps
           intro!: perfect_matching_max_card_matchingI
                   vs_make_perfect_matching max_card_matching_make_perfect_matching
           dest: max_card_matchingD)

end