theory Ranking2
  imports
    More_Graph
    More_List_Index
begin

sledgehammer_params [provers = cvc4 vampire verit e spass z3 zipperposition]


fun step :: "'a graph \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a graph \<Rightarrow> 'a graph" where
  "step _ _ [] M = M"
| "step G u (v#vs) M = (
      if v \<notin> Vs M \<and> u \<notin> Vs M \<and> {u,v} \<in> G
      then insert {u,v} M
      else step G u vs M
    )"

fun ranking' :: "'a graph \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a graph \<Rightarrow> 'a graph" where
  "ranking' _ [] _ M = M"
| "ranking' G (u#us) \<sigma> M = ranking' G us \<sigma> (step G u \<sigma> M)"

lemma ranking_foldl: "ranking' G \<pi> \<sigma> M = foldl (\<lambda>M u. step G u \<sigma> M) M \<pi>"
  by (induction G \<pi> \<sigma> M rule: ranking'.induct) auto

abbreviation "ranking G \<pi> \<sigma> \<equiv> ranking' G \<pi> \<sigma> {}"

definition ranking_matching :: "'a graph \<Rightarrow> 'a graph \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "ranking_matching G M \<pi> \<sigma> \<equiv> matching M \<and> M \<subseteq> G \<and>
    bipartite G (set \<pi>) (set \<sigma>) \<and> maximal_matching G M \<and>
    (\<forall>u v v'. ({u,v}\<in>M \<and> {u,v'}\<in>G \<and> index \<sigma> v' < index \<sigma> v) \<longrightarrow> (\<exists>u'. {u',v'}\<in>M \<and> index \<pi> u' < index \<pi> u)) \<and>
    (\<forall>u v u'. ({u,v}\<in>M \<and> {u',v}\<in>G \<and> index \<pi> u' < index \<pi> u) \<longrightarrow> (\<exists>v'. {u',v'}\<in>M \<and> index \<sigma> v' < index \<sigma> v))"

lemma ranking_matchingD:
  assumes "ranking_matching G M \<pi> \<sigma>"
  shows "graph_abs G \<and> M \<subseteq> G \<and> bipartite G (set \<pi>) (set \<sigma>) \<and> maximal_matching G M \<and>
    bipartite M (set \<pi>) (set \<sigma>) \<and> graph_abs M"
  using assms
  unfolding ranking_matching_def
  by (auto intro: bipartite_subgraph graph_abs_subgraph finite_bipartite_graph_abs)

lemma ranking_matching_commute:
  assumes "ranking_matching G M \<pi> \<sigma>"
  shows "ranking_matching G M \<sigma> \<pi>"
  using assms
  unfolding ranking_matching_def
  apply (auto simp: insert_commute bipartite_commute)
  by (metis (no_types, opaque_lifting) insert_commute)

lemma ranking_matching_bipartite_edges:
  assumes "ranking_matching G M \<pi> \<sigma>"
  assumes "{u,v} \<in> M"
  assumes "u \<in> set \<pi>"
  shows "v \<in> set \<sigma>"
  using assms
  unfolding ranking_matching_def bipartite_def
  by (metis disjoint_iff_not_equal doubleton_eq_iff in_mono)

lemma ranking_matching_bipartite_edges':
  assumes "ranking_matching G M \<pi> \<sigma>"
  assumes "{u,v} \<in> M"
  assumes "v \<in> set \<sigma>"
  shows "u \<in> set \<pi>"
  using assms
  unfolding ranking_matching_def bipartite_def
  by (metis disjoint_iff_not_equal doubleton_eq_iff in_mono)


lemma ranking_matching_maximalE:
  assumes "ranking_matching G M \<pi> \<sigma>"
  assumes "{u,v} \<in> G"
  obtains e where "e \<in> M" "u \<in> e \<or> v \<in> e"
  using assms
  by (auto dest: ranking_matchingD elim!: maximal_matching_edgeE)

lemma ranking_matching_earlier_match_onlineE:
  assumes "ranking_matching G M \<pi> \<sigma>"
  assumes "{u,v} \<in> M"
  assumes "{u,v'} \<in> G"
  assumes "index \<sigma> v' < index \<sigma> v"
  obtains u' where "{u',v'} \<in> M" "index \<pi> u' < index \<pi> u"
  using assms
  unfolding ranking_matching_def
  by (meson edges_are_Vs edges_are_walks walk_endpoints(2))

lemma ranking_matching_earlier_match_offlineE:
  assumes "ranking_matching G M \<pi> \<sigma>"
  assumes "{u,v} \<in> M"
  assumes "{u',v} \<in> G"
  assumes "index \<pi> u' < index \<pi> u"
  obtains v' where "{u',v'} \<in> M" "index \<sigma> v' < index \<sigma> v"
  using assms
  unfolding ranking_matching_def
  by (meson edges_are_Vs edges_are_walks walk_endpoints(2))

lemma ranking_matching_unique_match:
  assumes rm_M: "ranking_matching G M \<pi> \<sigma>"
  assumes rm_M': "ranking_matching G M' \<pi> \<sigma>"
  assumes v_M: "{u,v} \<in> M"
  assumes v'_M': "{u,v'} \<in> M'"
  assumes before: "index \<sigma> v' < index \<sigma> v"
  shows False
  using v_M v'_M' before
proof (induction "index \<pi> u" arbitrary: u v v' rule: less_induct)
  case less
  with rm_M rm_M' obtain u' where u': "{u',v'} \<in> M" "index \<pi> u' < index \<pi> u"
    by (meson ranking_matchingD ranking_matching_earlier_match_onlineE subsetD)

  with rm_M rm_M' \<open>{u,v'} \<in> M'\<close> obtain v'' where "{u',v''} \<in> M'" "index \<sigma> v'' < index \<sigma> v'"
    by (meson ranking_matchingD ranking_matching_earlier_match_offlineE subsetD)

  with less u' show ?case
    by blast
qed

lemma ranking_matching_unique_match':
  assumes rm_M: "ranking_matching G M \<pi> \<sigma>"
  assumes rm_M': "ranking_matching G M' \<pi> \<sigma>"
  assumes u_M: "{u,v} \<in> M"
  assumes u'_M': "{u',v} \<in> M'"
  assumes before: "index \<pi> u' < index \<pi> u"
  shows False
  using assms
  by (auto intro!: ranking_matching_unique_match dest: edge_commute ranking_matching_commute)


lemma ranking_matching_unique':
  assumes rm_M: "ranking_matching G M \<pi> \<sigma>"
  assumes rm_M': "ranking_matching G M' \<pi> \<sigma>"
  assumes "u \<in> set \<pi>" "v \<in> set \<sigma>"
  assumes "{u,v} \<in> M"
  shows "{u,v} \<in>  M'"
proof (rule ccontr)
  assume "{u,v} \<notin> M'"
  with rm_M' rm_M \<open>{u,v} \<in> M\<close> consider (u_matched) "u \<in> Vs M'" | (v_matched) "v \<in> Vs M'"
    by (auto dest!: ranking_matchingD elim!: maximal_matching_edgeE)

  then show False
  proof cases
    case u_matched
    then obtain v' where "{u,v'} \<in> M'"
      by (meson graph_abs_no_edge_no_vertex ranking_matchingD rm_M')

    with assms \<open>{u,v} \<notin> M'\<close> show False
      by (metis index_eq_index_conv nat_neq_iff ranking_matching_unique_match)    
  next
    case v_matched
    then obtain u' where "{u',v} \<in> M'"
      by (metis graph_abs_no_edge_no_vertex insert_commute ranking_matchingD rm_M')

    with assms \<open>{u,v} \<notin> M'\<close> show ?thesis
      by (metis index_eq_index_conv nat_neq_iff ranking_matching_unique_match')    
  qed
qed

lemma ranking_matching_unique'':
  assumes rm_M: "ranking_matching G M \<pi> \<sigma>"
  assumes "ranking_matching G M' \<pi> \<sigma>"
  assumes "e \<in> M"
  shows "e \<in> M'"
  using assms
proof -
  from rm_M \<open>e \<in> M\<close> obtain u v where "e = {u,v}" "u \<in> set \<pi>" "v \<in> set \<sigma>"
    by (auto dest: ranking_matchingD elim: bipartite_edgeE)

  with assms show ?thesis
    by (auto intro: ranking_matching_unique')
qed

lemma ranking_matching_unique:
  assumes "ranking_matching G M \<pi> \<sigma>"
  assumes "ranking_matching G M' \<pi> \<sigma>"
  shows "M = M'"
  using assms
  by (auto intro: ranking_matching_unique'')


definition remove_vertices_graph :: "'a graph \<Rightarrow> 'a set \<Rightarrow> 'a graph" (infixl "\<setminus>" 60) where
  "G \<setminus> X \<equiv> {e. e \<in> G \<and> e \<inter> X = {}}"

lemma remove_vertices_empty:
  "G \<setminus> {} = G"
  unfolding remove_vertices_graph_def by simp

lemma remove_vertices_not_vs:
  "v \<in> X \<Longrightarrow> v \<notin> Vs (G \<setminus> X)"
  unfolding Vs_def remove_vertices_graph_def by blast

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

lemma remove_edge_ranking_matching:
  "{u,v} \<in> M \<Longrightarrow> ranking_matching G M \<pi> \<sigma> \<Longrightarrow> ranking_matching (G \<setminus> {u,v}) (M \<setminus> {u,v}) \<pi> \<sigma>"
  unfolding ranking_matching_def
  apply (intro conjI)
       apply (meson matching_subgraph remove_vertices_subgraph)
      apply (meson remove_vertices_mono subsetI)
     apply (meson bipartite_remove_vertices)
  apply (smt (verit, ccfv_threshold) DiffI edges_are_walks insertI1 matching_subgraph maximal_matching_def remove_edge_matching_vs remove_vertices_not_vs remove_vertices_subgraph subset_eq vs_member_intro walk_endpoints(2))
   apply (metis edges_are_walks in_remove_verticesI insert_subset matching_def remove_vertices_not_vs remove_vertices_subgraph' subset_insertI walk_endpoints(2))
  by (metis edges_are_Vs in_remove_verticesI insertI1 matching_def remove_vertices_not_vs remove_vertices_subgraph')
  
definition remove_vertices_rank :: "'a list \<Rightarrow> 'a set \<Rightarrow> 'a list" (infix "\<setminus>" 60) where
  "\<sigma> \<setminus> X \<equiv> [v <- \<sigma>. v \<notin> X]"

lemma remove_vertices_not_in_rank:
  "v \<in> X \<Longrightarrow> v \<notin> set (\<sigma> \<setminus> X)"
  unfolding remove_vertices_rank_def
  by simp



definition "shifts_to G M u v v' \<pi> \<sigma> \<equiv>
  \<comment> \<open>v' comes after v and there's an edge to u\<close>
  u \<in> set \<pi> \<and> v' \<in> set \<sigma> \<and> index \<sigma> v < index \<sigma> v' \<and> {u,v'} \<in> G \<and>
  \<comment> \<open>but v' is not matched to some u' before u\<close>
    (\<nexists>u'. index \<pi> u' < index \<pi> u \<and> {u',v'} \<in> M) \<and>
  \<comment> \<open>every other vertex between v and v' is not connected to u or matched to some u' before u\<close>
    (\<forall>v''. (index \<sigma> v < index \<sigma> v'' \<and> index \<sigma> v'' < index \<sigma> v') \<longrightarrow>
      ({u,v''} \<notin> G \<or> (\<exists>u'. index \<pi> u' < index \<pi> u \<and> {u',v''} \<in> M)))"

function zig :: "'a graph \<Rightarrow> 'a graph \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
and zag :: "'a graph \<Rightarrow> 'a graph \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  proper_zig: "zig G M v \<pi> \<sigma> = v # (
                    if \<exists>u. {u,v} \<in> M 
                    then zag G M (THE u. {u,v} \<in> M) \<pi> \<sigma>
                    else [])" if "matching M"
| no_matching_zig: "zig _ M _ _ _ = []" if "\<not>matching M"

| proper_zag: "zag G M u \<pi> \<sigma> =  u # (if \<exists>v. {u,v} \<in> M
                      then 
                      (let v = THE v. {u,v} \<in> M in (
                        if \<exists>v'. shifts_to G M u v v' \<pi> \<sigma>
                        then zig G M (THE v'. shifts_to G M u v v' \<pi> \<sigma>) \<pi> \<sigma>
                        else [])
                      )
                      else []
                    )" if "matching M"
| no_matching_zag: "zag _ M _ _ _ = []" if "\<not>matching M"
  by auto (smt (z3) prod_cases5 sum.collapse)

definition zig_zag_relation where
  "zig_zag_relation \<equiv>
    {(Inr (G, M, u, \<pi>, \<sigma>), Inl (G, M, v, \<pi>, \<sigma>)) | (G :: 'a graph) M u v \<pi> \<sigma>. matching M \<and> {u,v} \<in> M \<and> ((\<exists>v'. shifts_to G M u v v' \<pi> \<sigma>) \<longrightarrow> index \<sigma> v < index \<sigma> (THE v'. shifts_to G M u v v' \<pi> \<sigma>))} \<union>
    {(Inl (G, M, v', \<pi>, \<sigma>), Inr (G, M, u, \<pi>, \<sigma>)) | (G :: 'a graph) M u v' \<pi> \<sigma>. matching M \<and> (\<exists>v. {u,v} \<in> M \<and> shifts_to G M u (THE v. {u,v} \<in> M) v' \<pi> \<sigma>) \<and> index \<sigma> (THE v. {u,v} \<in> M) < index \<sigma> v'}"


lemma the_match: "matching M \<Longrightarrow> {u,v} \<in> M \<Longrightarrow> (THE u. {u,v} \<in> M) = u"
  apply (auto intro!: the_equality )
  by (metis doubleton_eq_iff insertI1 matching_unique_match)

lemma the_match': "matching M \<Longrightarrow> {u,v} \<in> M \<Longrightarrow> (THE v. {u,v} \<in> M) = v"
  apply (auto intro!: the_equality)
  by (metis (mono_tags, lifting) insert_commute the_match)

lemma shifts_to_only_from_input:
  assumes "shifts_to G M u v v' \<pi> \<sigma>"
  shows "v \<in> set \<sigma>" "v' \<in> set \<sigma>"
  using assms
  unfolding shifts_to_def
   apply (metis index_conv_size_if_notin index_le_size leD)
  by (metis assms shifts_to_def)

lemma shifts_to_inj:
  assumes "shifts_to G M u v v' \<pi> \<sigma>"
  assumes "shifts_to G M u v v'' \<pi> \<sigma>"
  shows "v' = v''"
  using assms
  unfolding shifts_to_def
  by (metis index_eq_index_conv not_less_iff_gr_or_eq)

lemma the_shifts_to:
  assumes "shifts_to G M u v v' \<pi> \<sigma>"
  shows "(THE v'. shifts_to G M u v v' \<pi> \<sigma>) = v'"
  using assms
  by (auto dest: shifts_to_inj)

lemma zig_zag_relation_unique:
  "(y,x) \<in> zig_zag_relation \<Longrightarrow> (y',x) \<in> zig_zag_relation \<Longrightarrow> y = y'"
  unfolding zig_zag_relation_def
  by (auto dest: the_match shifts_to_inj)

lemma zig_zag_relation_increasing_rank:
  assumes "(Inr (G, M, u, \<pi>, \<sigma>), Inl (G, M, v, \<pi>, \<sigma>)) \<in> zig_zag_relation"
  assumes "(Inl (G, M, v', \<pi>, \<sigma>), Inr (G, M, u, \<pi>, \<sigma>)) \<in> zig_zag_relation"
  shows "index \<sigma> v < index \<sigma> v'"
proof -
  from \<open>(Inr (G, M, u, \<pi>, \<sigma>), Inl (G, M, v, \<pi>, \<sigma>)) \<in> zig_zag_relation\<close> have "matching M"
    "{u,v} \<in> M"
    unfolding zig_zag_relation_def
    by auto

  then have "(THE v. {u,v} \<in> M) = v" by (auto intro: the_match')

  with \<open>(Inl (G, M, v', \<pi>, \<sigma>), Inr (G, M, u, \<pi>, \<sigma>)) \<in> zig_zag_relation\<close> show ?thesis
    unfolding zig_zag_relation_def
    by simp
qed


lemma wf_zig_zag_relation_Inl_aux:
  assumes "\<forall>x. (\<forall>y. (y,x) \<in> zig_zag_relation \<longrightarrow> P y) \<longrightarrow> P x"
  shows "P (Inl a)"
proof (cases a)
  case (fields G M v \<pi> \<sigma>)
  have PI: "\<And>x. (\<And>y. (y,x) \<in> zig_zag_relation \<Longrightarrow> P y) \<Longrightarrow> P x" using assms by blast

  have "P (Inl (G, M, v, \<pi>, \<sigma>))"
  proof (induction "length \<sigma> - index \<sigma> v" arbitrary: v rule: less_induct)
    case less
    then show ?case
    proof (cases "\<exists>y. (y, Inl (G, M, v, \<pi>, \<sigma>)) \<in> zig_zag_relation")
      case True
      then obtain u where "(Inr (G, M, u, \<pi>, \<sigma>), Inl (G, M, v, \<pi>, \<sigma>)) \<in> zig_zag_relation"
        unfolding zig_zag_relation_def by auto

      then have "\<And>y. (y, Inl (G, M, v, \<pi>, \<sigma>)) \<in> zig_zag_relation \<Longrightarrow> y = Inr (G, M, u, \<pi>, \<sigma>)"
        by (simp add: zig_zag_relation_unique)

      show ?thesis
      proof (cases "\<exists>x'. (x', Inr (G, M, u, \<pi>, \<sigma>)) \<in> zig_zag_relation")
        case True
        then obtain v' where "(Inl (G, M, v', \<pi>, \<sigma>), Inr (G, M, u, \<pi>, \<sigma>)) \<in> zig_zag_relation"
          unfolding zig_zag_relation_def by auto

        then have "\<And>x'. (x', Inr (G, M, u, \<pi>, \<sigma>)) \<in> zig_zag_relation \<Longrightarrow> x' = Inl (G, M, v', \<pi>, \<sigma>)"
          by (simp add: zig_zag_relation_unique)

        have "P (Inl (G, M, v', \<pi>, \<sigma>))"
          using \<open>(Inr (G, M, u, \<pi>, \<sigma>), Inl (G, M, v, \<pi>, \<sigma>)) \<in> zig_zag_relation\<close>
            \<open>(Inl (G, M, v', \<pi>, \<sigma>), Inr (G, M, u, \<pi>, \<sigma>)) \<in> zig_zag_relation\<close>
          by (auto intro!: less zig_zag_relation_increasing_rank simp: length_minus_index_less_index_gt)

        then have "P (Inr (G, M, u, \<pi>, \<sigma>))"
          using PI \<open>\<And>x'. (x', Inr (G, M, u, \<pi>, \<sigma>)) \<in> zig_zag_relation \<Longrightarrow> x' = Inl (G, M, v', \<pi>, \<sigma>)\<close> by blast

        then show ?thesis
          using PI \<open>\<And>y. (y, Inl (G, M, v, \<pi>, \<sigma>)) \<in> zig_zag_relation \<Longrightarrow> y = Inr (G, M, u, \<pi>, \<sigma>)\<close> by blast
      next
        case False
        then show ?thesis
          using PI \<open>(Inr (G, M, u, \<pi>, \<sigma>), Inl (G, M, v, \<pi>, \<sigma>)) \<in> zig_zag_relation\<close> zig_zag_relation_unique by blast
      qed
    next
      case False
      then show ?thesis
        using \<open>\<forall>x. (\<forall>y. (y, x) \<in> zig_zag_relation \<longrightarrow> P y) \<longrightarrow> P x\<close> by blast
    qed
  qed
  with fields show ?thesis by simp
qed

lemma wf_zig_zag_relation_aux:
  assumes "\<forall>x. (\<forall>y. (y,x) \<in> zig_zag_relation \<longrightarrow> P y) \<longrightarrow> P x"
  shows "P x"
proof -
  have PI: "\<And>x. (\<And>y. (y,x) \<in> zig_zag_relation \<Longrightarrow> P y) \<Longrightarrow> P x" using assms by blast
  show "P x"
  proof (cases x)
    case Inl
    with assms wf_zig_zag_relation_Inl_aux show ?thesis by blast
  next
    case (Inr b)
    then show ?thesis
    proof (cases "\<exists>y. (y, Inr b) \<in> zig_zag_relation")
      case True
      then obtain a where "(Inl a, Inr b) \<in> zig_zag_relation" 
        unfolding zig_zag_relation_def by blast

      then have "\<And>y. (y, Inr b) \<in> zig_zag_relation \<Longrightarrow> y = Inl a"
        by (simp add: zig_zag_relation_unique)

      have "P (Inl a)" using assms wf_zig_zag_relation_Inl_aux by blast

      then show ?thesis
        using Inr PI \<open>\<And>y. (y, Inr b) \<in> zig_zag_relation \<Longrightarrow> y = Inl a\<close> by blast
    next
      case False
      then show ?thesis
        using Inr PI by blast
    qed
  qed
qed

lemma wf_zig_zag_relation: "wf zig_zag_relation"
  using wf_def wf_zig_zag_relation_aux by auto

termination zig
  apply (relation zig_zag_relation)
  apply (rule wf_zig_zag_relation)
  unfolding zig_zag_relation_def
  apply auto
  subgoal by (auto simp: the_match)
  subgoal for M G v \<pi> \<sigma> u v'
  proof -
    assume assms: "matching M" "{u,v} \<in> M" "shifts_to G M (THE u. {u, v} \<in> M) v v' \<pi> \<sigma>"
    then have the_u: "(THE u. {u,v} \<in> M) = u" 
      by (auto intro: the_match)

    with assms have "(THE v'. shifts_to G M u v v' \<pi> \<sigma>) = v'"
      using the_shifts_to by fastforce

    with the_u show ?thesis
      by (metis assms(3) shifts_to_def)
  qed
  subgoal for M G u \<pi> \<sigma> v v'
  proof -
    assume assms: "matching M" "{u,v} \<in> M" "shifts_to G M u (THE v. {u,v} \<in> M) v' \<pi> \<sigma>"

    then have the_v: "(THE v. {u,v} \<in> M) = v"
      by (auto intro: the_match')

    with assms have "(THE v'. shifts_to G M u v v' \<pi> \<sigma>) = v'"
      using the_shifts_to by fastforce

    with assms the_v show ?thesis
      using shifts_to_def the_v by fastforce
  qed
  subgoal for M G u \<pi> \<sigma> v v'
  proof -
    assume assms: "matching M" "{u,v} \<in> M" "shifts_to G M u (THE v. {u,v} \<in> M) v' \<pi> \<sigma>"
    then have the_v: "(THE v. {u,v} \<in> M) = v" 
      by (auto intro: the_match')

    with assms have "(THE v'. shifts_to G M u v v' \<pi> \<sigma>) = v'"
      using the_shifts_to by fastforce
    with the_v assms show ?thesis
      by (simp add: shifts_to_def)
  qed
  done

thm zig_zag.induct
declare zig.simps[simp del] zag.simps[simp del]

fun_cases zig_ConsE: "zig G M v \<pi> \<sigma> = v' # uvs"
fun_cases zig_NilE: "zig G M v \<pi> \<sigma> = []"
thm zig_ConsE zig_NilE

fun_cases zag_ConsE: "zag G M u \<pi> \<sigma> = u' # uvs"
fun_cases zag_NilE: "zag G M u \<pi> \<sigma> = []"
thm zag_ConsE zag_NilE


lemma zig_matching_edge: "zig G M v \<pi> \<sigma> = v # u # uvs \<Longrightarrow> {u,v} \<in> M"
  by (auto elim!: zig_ConsE split: if_splits simp: the_match zag.simps)

lemma zag_shift_edge:
  assumes "{u,v} \<in> M"
  assumes "zag G M u \<pi> \<sigma> = u # v' # uvs"
  shows "shifts_to G M u v v' \<pi> \<sigma>"
proof -
  have the_v: "(THE v. {u,v} \<in> M) = v" 
    using assms zag_ConsE the_match' by fast

  with assms have has_shift: "\<exists>v'. shifts_to G M u v v' \<pi> \<sigma>"
    by (smt (verit, ccfv_threshold) list.inject list.simps(3) the_match' zag.simps)

  then obtain v'' where shifts_to: "shifts_to G M u v v'' \<pi> \<sigma>" by blast
  with the_shifts_to have "(THE v'. shifts_to G M u v v' \<pi> \<sigma>) = v''"
    by fastforce

  with assms the_v has_shift have "v'' = v'"
    by (auto elim: zag_ConsE split: if_splits simp: Let_def zig.simps)

  with shifts_to show ?thesis by simp
qed

lemma 
  assumes "zig G M v \<pi> \<sigma> = v # u # v' # uvs"
  shows "index \<sigma> v < index \<sigma> v'"
proof -
  have "{u,v} \<in> M" using assms zig_matching_edge by fast
  then have "(THE u. {u,v} \<in> M) = u" using assms the_match zig_ConsE by fast
  with \<open>{u,v} \<in> M\<close> assms have "zig G M v \<pi> \<sigma> = v # zag G M u \<pi> \<sigma>"
    by (auto elim!: zig_ConsE intro: the_match)

  with assms \<open>{u,v} \<in> M\<close> have "shifts_to G M u v v' \<pi> \<sigma>"
    by (auto dest: zag_shift_edge)

  then show ?thesis unfolding shifts_to_def by blast
qed

lemma step_already_matched:
  "u \<in> Vs M \<Longrightarrow> step G u \<sigma> M = M"
  by (induction \<sigma>) auto

lemma step_mono:
  "e \<in> M \<Longrightarrow> e \<in> step G u \<sigma> M"
  by (induction \<sigma>) auto

lemma step_mono_vs:
  "v \<in> Vs M \<Longrightarrow> v \<in> Vs (step G u \<sigma> M)"
  by (induction \<sigma>) (auto simp: Vs_def)


lemma step_ConsI:
  assumes "v \<notin> Vs M \<Longrightarrow> u \<notin> Vs M \<Longrightarrow> {u,v} \<in> G \<Longrightarrow> P (insert {u,v} M)"
  assumes "v \<in> Vs M \<or> u \<in> Vs M \<or> {u,v} \<notin> G \<Longrightarrow> P (step G u vs M)"
  shows "P (step G u (v#vs) M)"
  using assms by simp

lemma edge_in_step:
  assumes "e \<in> step G u \<sigma> M"
  shows "e \<in> M \<or> (\<exists>v. e = {u,v} \<and> v \<in> set \<sigma> - Vs M \<and> {u,v} \<in> G \<and> 
                      (\<forall>v'\<in> set \<sigma> \<inter> {v''. {u,v''} \<in> G} - Vs M - {v}. index \<sigma> v < index \<sigma> v'))"
  using assms
proof (induction G u \<sigma> M rule: step.induct)
  case (2 G u v vs M)
  consider (match) "v \<notin> Vs M" "{u,v} \<in> G" "u \<notin> Vs M" | (ind) "v \<in> Vs M \<or> {u,v} \<notin> G \<or> u \<in> Vs M" by blast
  then show ?case 
  proof cases
    case match
    with 2 show ?thesis 
      by auto
  next
    case ind
    with 2 consider "e \<in> M" | "(\<exists>v. e = {u, v} \<and> v \<in> set vs - Vs M \<and> {u, v} \<in> G \<and> (\<forall>v'\<in>set vs \<inter> {v''. {u,v''} \<in> G} - Vs M - {v}. index vs v < index vs v'))"
      by fastforce
    then show ?thesis
    proof cases
      case 2
      then obtain w where w: "e = {u,w}" "w \<in> set vs - Vs M" "{u,w} \<in> G"
        "\<forall>v'\<in> set vs \<inter> {v''. {u,v''} \<in> G} - Vs M - {w}. index vs w < index vs v'" by blast
      have "v \<noteq> w"
        by (metis "2.prems" DiffD2 \<open>e = {u, w}\<close> \<open>w \<in> set vs - Vs M\<close> \<open>{u, w} \<in> G\<close> ind insert_subset step_already_matched subsetI vs_member_intro)
      with w have "\<forall>v'\<in> set (v#vs) \<inter> {v''. {u,v''} \<in> G} - Vs M - {w}. index (v#vs) w < index (v#vs) v'"
        apply simp
        by (smt (z3) "2.prems" Diff_iff IntE Int_commute Int_insert_right_if0 Int_insert_right_if1 edges_are_Vs ind insert_commute insert_iff mem_Collect_eq step_already_matched)
      then show ?thesis
        by (metis Diff_iff Diff_insert \<open>e = {u, w}\<close> \<open>w \<in> set vs - Vs M\<close> \<open>{u, w} \<in> G\<close> list.simps(15))
    qed simp
  qed
qed simp

lemma edge_matched_in_stepE:
  assumes "e \<in> step G u \<sigma> M"
  assumes "e \<notin> M"
  obtains v where "e = {u,v}" "v \<in> set \<sigma> \<inter> {v'. {u,v'} \<in> G} - Vs M"
    "\<forall>v'\<in> set \<sigma> \<inter> {v''. {u,v''} \<in> G} - Vs M - {v}. index \<sigma> v < index \<sigma> v'"
  using assms edge_in_step
  by force

lemma step_no_match_id:
  assumes "u \<in> Vs M \<or> \<not>(\<exists>v \<in> set \<sigma>. v \<notin> Vs M \<and> {u,v} \<in> G)"
  shows "step G u \<sigma> M = M"
  using assms
  by (induction G u \<sigma> M rule: step.induct) auto

lemma step_matches_if_possible:
  assumes "u \<notin> Vs M"
  assumes "v \<in> set \<sigma>" "v \<notin> Vs M"
  assumes "{u,v} \<in> G"
  shows "\<exists>v. {u,v} \<in> step G u \<sigma> M"
  using assms
proof (induction G u \<sigma> M rule: step.induct)
  case (2 G u v' vs M)
  then show ?case
  proof (cases "v = v'")
    case True
    with 2 show ?thesis
      by auto
  next
    case False
    then consider (match) "v' \<notin> Vs M \<and> {u,v'} \<in> G" | (prev_match) "v' \<in> Vs M" | (not_connected) "{u,v'} \<notin> G" by blast

    then show ?thesis
      by cases (use 2 in auto)
  qed
qed simp

lemma graph_abs_step:
  assumes "graph_abs G"
  assumes "graph_abs M"
  shows "graph_abs (step G u \<sigma> M)"
  using assms
  by (induction \<sigma>) (auto dest: graph_abs_edgeD)

lemma matching_step:
  assumes "matching M"
  assumes "u \<notin> set \<sigma>"
  shows "matching (step G u \<sigma> M)"
  using assms
  by (induction \<sigma>) (auto simp: matching_def)

lemma step_matches_graph_edge:
  assumes "M \<subseteq> G"
  shows "step G u \<sigma> M \<subseteq> G"
  using assms
  by (induction \<sigma>) auto

lemma ranking_mono: "e \<in> M \<Longrightarrow> e \<in> ranking' G \<pi> \<sigma> M"
  by (induction G \<pi> \<sigma> M rule: ranking'.induct)
     (auto simp: step_mono)

lemma ranking_mono_vs: "x \<in> Vs M \<Longrightarrow> x \<in> Vs (ranking' G \<pi> \<sigma> M)"
  by (meson ranking_mono vs_member)

lemma bipartite_step:
  assumes "bipartite G (set \<pi>) (set \<sigma>)"
  assumes "M \<subseteq> G"
  shows "bipartite (step G u \<sigma> M) (set \<pi>) (set \<sigma>)"
  using assms
  by (auto dest: step_matches_graph_edge intro: bipartite_subgraph)

lemma graph_abs_ranking':
  assumes "graph_abs G"
  assumes "graph_abs M"
  shows "graph_abs (ranking' G \<pi> \<sigma> M)"
  using assms
  by (induction \<pi> arbitrary: M) (auto dest: graph_abs_step)

lemma matching_ranking':
  assumes "matching M"
  assumes "set \<pi> \<inter> set \<sigma> = {}"
  shows "matching (ranking' G \<pi> \<sigma> M)"
  using assms
  by (induction \<pi> arbitrary: M) (auto dest: matching_step)

lemma matching_ranking: "set \<pi> \<inter> set \<sigma> = {} \<Longrightarrow> matching (ranking G \<pi> \<sigma>)"
  by (auto intro: matching_ranking')

lemma subgraph_ranking':
  assumes "M \<subseteq> G"
  shows "ranking' G \<pi> \<sigma> M \<subseteq> G"
  using assms
  by (induction \<pi> arbitrary: M) (auto simp: step_matches_graph_edge)

lemma bipartite_ranking':
  assumes "bipartite G (set \<pi>) (set \<sigma>)"
  assumes "M \<subseteq> G"
  shows "bipartite (ranking' G \<pi> \<sigma> M) (set \<pi>) (set \<sigma>)"
  using assms
  by (auto intro: bipartite_subgraph dest: subgraph_ranking')


lemma maximal_ranking_aux:
  assumes "{u,v} \<in> G"
  assumes "u \<in> set \<pi>" "v \<in> set \<sigma>"
  assumes "set \<pi> \<inter> set \<sigma> = {}"
  assumes "u \<notin> Vs (ranking G \<pi> \<sigma>)" "v \<notin> Vs (ranking G \<pi> \<sigma>)"
  shows False
proof -
  from \<open>u \<in> set \<pi>\<close> obtain us us' where "\<pi> = us @ u # us'"
    by (auto dest: split_list)

  then have ranking_unfold: "ranking G \<pi> \<sigma> = ranking' G us' \<sigma> (step G u \<sigma> (ranking G us \<sigma>))"
    by (simp add: ranking_foldl)

  with \<open>u \<notin> Vs (ranking G \<pi> \<sigma>)\<close> \<open>v \<notin> Vs (ranking G \<pi> \<sigma>)\<close> have "u \<notin> Vs (ranking G us \<sigma>)" "v \<notin> Vs (ranking G us \<sigma>)"
    by (auto dest: ranking_mono_vs step_mono_vs)

  with \<open>{u,v} \<in> G\<close> \<open>u \<in> set \<pi>\<close> \<open>v \<in> set \<sigma>\<close> obtain v' where "{u,v'} \<in> step G u \<sigma> (ranking G us \<sigma>)"
    by (auto dest: step_matches_if_possible)

  then have "{u,v'} \<in> ranking G \<pi> \<sigma>"
    by (simp add: ranking_unfold ranking_mono)

  with \<open>u \<notin> Vs (ranking G \<pi> \<sigma>)\<close> show False by auto
qed

lemma maximal_ranking:
  assumes bipartite: "bipartite G (set \<pi>) (set \<sigma>)"
  shows "maximal_matching G (ranking G \<pi> \<sigma>)"
proof (rule ccontr)
  assume "\<not>maximal_matching G (ranking G \<pi> \<sigma>)"

  with bipartite_disjointD[OF assms] matching_ranking[of \<pi> \<sigma> G]
  obtain u v where unmatched: "{u,v} \<in> G" "u \<notin> Vs (ranking G \<pi> \<sigma>)" "v \<notin> Vs (ranking G \<pi> \<sigma>)"
    by (auto elim: not_maximal_matchingE)

  with bipartite consider "u \<in> set \<pi>" "v \<in> set \<sigma>" | "u \<in> set \<sigma>" "v \<in> set \<pi>"
    by (metis bipartite_edgeE doubleton_eq_iff)

  then show False
    by cases 
       (use unmatched \<open>set \<pi> \<inter> set \<sigma> = {}\<close> in \<open>auto intro: maximal_ranking_aux dest: edge_commute\<close>)
qed



subsection \<open>Removing vertices\<close>
lemma remove_vertices_graph_disjoint: "X \<inter> Vs G = {} \<Longrightarrow> G \<setminus> X = G"
  unfolding Vs_def remove_vertices_graph_def by blast

lemma remove_vertex_not_in_graph: "x \<notin> Vs G \<Longrightarrow> G \<setminus> {x} = G"
  by (auto intro!: remove_vertices_graph_disjoint)

lemma remove_vertices_rank_disjoint: "X \<inter> set \<sigma> = {} \<Longrightarrow> \<sigma> \<setminus> X = \<sigma>"
  unfolding remove_vertices_rank_def
  by (auto intro: filter_True)

lemma remove_vertex_not_in_rank: "x \<notin> set \<sigma> \<Longrightarrow> \<sigma> \<setminus> {x} = \<sigma>"
  by (auto intro: remove_vertices_rank_disjoint)

lemma step_u_not_in_graph:
  "u \<notin> Vs G \<Longrightarrow> step G u \<sigma> M = M"
  by (induction G u \<sigma> M rule: step.induct)
     (auto dest: edges_are_Vs)

lemma ranking'_remove_vertices_graph_remove_vertices_arrival:
  "ranking' (G \<setminus> X) (\<pi> \<setminus> X) \<sigma> M = ranking' (G \<setminus> X) \<pi> \<sigma> M"
  by (induction "G \<setminus> X" \<pi> \<sigma> M rule: ranking'.induct)
     (auto simp: remove_vertices_rank_def remove_vertices_not_vs step_u_not_in_graph)

lemma ranking_remove_vertices_graph_remove_vertices_arrival:
  "ranking (G \<setminus> X) (\<pi> \<setminus> X) \<sigma> = ranking (G \<setminus> X) \<pi> \<sigma>"
  using ranking'_remove_vertices_graph_remove_vertices_arrival
  by blast

lemma step_remove_vertices_graph_remove_vertices_rank:
  "step (G \<setminus> X) u (\<sigma> \<setminus> X) M = step (G \<setminus> X) u \<sigma> M"
  by (induction "G \<setminus> X" u \<sigma> M rule: step.induct)
     (simp_all add: remove_vertices_rank_def remove_vertices_graph_def)

lemma ranking'_remove_vertices_graph_remove_vertices_rank:
  "ranking' (G \<setminus> X) \<pi> (\<sigma> \<setminus> X) M = ranking' (G \<setminus> X) \<pi> \<sigma> M"
  by (induction "G \<setminus> X" \<pi> \<sigma> M rule: ranking'.induct)
     (simp_all add: step_remove_vertices_graph_remove_vertices_rank)

lemma ranking_remove_vertices_graph_remove_vertices_rank:
  "ranking (G \<setminus> X) \<pi> (\<sigma> \<setminus> X) = ranking (G \<setminus> X) \<pi> \<sigma>"
  using ranking'_remove_vertices_graph_remove_vertices_rank
  by blast

locale wf_ranking =
  fixes G :: "'a graph"
    and \<pi> :: "'a list"
    and \<sigma> :: "'a list"
  assumes "graph_abs G"
      and bipartite_graph: "partitioned_bipartite G (set \<sigma>)"
      and "distinct \<sigma>"
      and "distinct \<pi>"
      and bipartite_input: "set \<sigma> \<inter> set \<pi> = {}"
      and vs_subset: "Vs G \<subseteq> set \<sigma> \<union> set \<pi>"
begin

lemma bipartite_graph': "partitioned_bipartite G (set \<pi>)"
  using partitioned_bipartite_swap[OF bipartite_graph vs_subset bipartite_input] .
  

end

lemma ranking'_rank_empty: "ranking' G \<pi> [] M = M"
  by (induction \<pi>) auto

lemma ranking'_Cons_rank_commute:
  "ranking' G \<sigma> (u # us) M = ranking' G us \<sigma> (step G u \<sigma> M)"
  oops

lemma ranking'_commute:
  "ranking' G \<pi> \<sigma> M = ranking' G \<sigma> \<pi> M"
  sorry


lemma shifts_to_mono: 
  assumes "G' \<subseteq> G"
  assumes "shifts_to G' M u v v' \<pi> \<sigma>"
  shows "\<exists>v'. shifts_to G M u v v' \<pi> \<sigma>"
proof -
  consider (same) "shifts_to G M u v v' \<pi> \<sigma>" | (earlier) "\<not>shifts_to G M u v v' \<pi> \<sigma>" by blast
  then show ?thesis
  proof (cases)
    case earlier
    with assms have "\<exists>v''. index \<sigma> v < index \<sigma> v'' \<and> index \<sigma> v'' < index \<sigma> v' \<and> {u,v''} \<in> G \<and> (\<nexists>u'. index \<pi> u' < index \<pi> u \<and> {u',v''} \<in> M)"
      unfolding shifts_to_def by blast

    then obtain v'' where "index \<sigma> v < index \<sigma> v'' \<and> index \<sigma> v'' < index \<sigma> v' \<and> {u,v''} \<in> G \<and> (\<nexists>u'. index \<pi> u' < index \<pi> u \<and> {u',v''} \<in> M)"
      by blast

    then show ?thesis
    proof (induction "index \<sigma> v''" arbitrary: v'' rule: less_induct)
      case less
      then show ?case
      proof (cases "shifts_to G M u v v'' \<pi> \<sigma>")
        case False
        have "v'' \<in> set \<sigma>" 
          using less
          by (auto intro: index_less_in_set)

        with False less have "\<exists>v'''. index \<sigma> v < index \<sigma> v''' \<and> index \<sigma> v''' < index \<sigma> v'' \<and> {u,v'''} \<in> G \<and> (\<nexists>u'. index \<pi> u' < index \<pi> u \<and> {u',v'''} \<in> M)"
          unfolding shifts_to_def
          by (metis assms(2) shifts_to_def)
        
        with less show ?thesis by auto
      qed blast
    qed
  qed blast
qed

lemma remove_offline_vertices_before_shifts_to_mono:
  assumes "set \<pi> \<inter> set \<sigma> = {}"
  assumes "X \<subseteq> set \<sigma>"
  assumes "\<forall>x \<in> X. index \<sigma> x < index \<sigma> v"
  assumes "shifts_to (G \<setminus> X) (M \<setminus> X) u v v' \<pi> \<sigma>"
  shows "\<exists>v'. shifts_to G M u v v' \<pi> \<sigma>"
proof -
  consider (same) "shifts_to G M u v v' \<pi> \<sigma>" | (earlier) "\<not>shifts_to G M u v v' \<pi> \<sigma>" by blast
  then show ?thesis
  proof cases
    case earlier
    with assms have "\<exists>v''. index \<sigma> v < index \<sigma> v'' \<and> index \<sigma> v'' < index \<sigma> v' \<and> {u,v''} \<in> G \<and> (\<nexists>u'. index \<pi> u' < index \<pi> u \<and> {u',v''} \<in> M)"
      unfolding shifts_to_def
      by (smt (verit, best) Diff_disjoint Diff_insert_absorb Int_insert_left_if0 disjoint_iff in_remove_verticesI index_less_in_set less_asym' remove_vertices_subgraph')

    then obtain v'' where "index \<sigma> v < index \<sigma> v''" "index \<sigma> v'' < index \<sigma> v'" "{u,v''} \<in> G" "\<nexists>u'. index \<pi> u' < index \<pi> u \<and> {u',v''} \<in> M"
      by blast

    then show ?thesis
    proof (induction "index \<sigma> v''" arbitrary: v'' rule: less_induct)
      case less
      then show ?case
      proof (cases "shifts_to G M u v v'' \<pi> \<sigma>")
        case False
        from \<open>index \<sigma> v'' < index \<sigma> v'\<close> have "v'' \<in> set \<sigma>"
          by (auto intro: index_less_in_set)

        with False less assms have "\<exists>v'''. index \<sigma> v < index \<sigma> v''' \<and> index \<sigma> v''' < index \<sigma> v'' \<and> {u,v'''} \<in> G \<and> (\<nexists>u'. index \<pi> u' < index \<pi> u \<and> {u',v'''} \<in> M)"
          unfolding shifts_to_def
          by blast

        with less show ?thesis by auto
      qed blast
    qed
  qed blast
qed

lemma remove_online_vertices_before_shifts_to_mono:
  assumes "set \<pi> \<inter> set \<sigma> = {}"
  assumes "X \<subseteq> set \<pi>"
  assumes "matching M"
  assumes "(\<forall>x \<in> X. ((\<exists>v. {x,v} \<in> M) \<longrightarrow> index \<sigma> (THE v. {x,v} \<in> M) < index \<sigma> v))"
  assumes "shifts_to (G \<setminus> X) (M \<setminus> X) u v v' \<pi> \<sigma>"
  shows "\<exists>v'. shifts_to G M u v v' \<pi> \<sigma>"
proof -
  {
    fix u'
    assume "{u',v'} \<in> M"

    with assms have "u' \<notin> X"
      by (auto simp: shifts_to_def the_match')

    with \<open>{u',v'} \<in> M\<close> have "{u',v'} \<in> M \<setminus> X"
      apply (auto intro!: in_remove_verticesI)
      by (meson assms(1) assms(2) assms(5) disjoint_iff shifts_to_only_from_input(2) subsetD)
  } note this

  consider (same) "shifts_to G M u v v' \<pi> \<sigma>" | (earlier) "\<not>shifts_to G M u v v' \<pi> \<sigma>" by blast

  then show ?thesis
  proof cases
    case earlier
    with assms have "\<exists>v''. index \<sigma> v < index \<sigma> v'' \<and> index \<sigma> v'' < index \<sigma> v' \<and> {u,v''} \<in> G \<and> (\<nexists>u'. index \<pi> u' < index \<pi> u \<and> {u',v''} \<in> M)"
      unfolding shifts_to_def
      by (meson \<open>\<And>u'. {u', v'} \<in> M \<Longrightarrow> {u', v'} \<in> M \<setminus> X\<close> remove_vertices_subgraph')

    then obtain v'' where "index \<sigma> v < index \<sigma> v''" "index \<sigma> v'' < index \<sigma> v'" "{u,v''} \<in> G" "(\<nexists>u'. index \<pi> u' < index \<pi> u \<and> {u',v''} \<in> M)"
      by blast

    then show ?thesis
    proof (induction "index \<sigma> v''" arbitrary: v'' rule: less_induct)
      case less
      then show ?case
      proof (cases "shifts_to G M u v v'' \<pi> \<sigma>")
        case False
        from \<open>index \<sigma> v'' < index \<sigma> v'\<close> have "v'' \<in> set \<sigma>"
          by (auto intro: index_less_in_set)

        with False less assms have "\<exists>v'''. index \<sigma> v < index \<sigma> v''' \<and> index \<sigma> v''' < index \<sigma> v'' \<and> {u,v'''} \<in> G \<and> (\<nexists>u'. index \<pi> u' < index \<pi> u \<and> {u',v'''} \<in> M)"
          unfolding shifts_to_def
          by blast

        with less show ?thesis by auto
      qed blast
    qed
  qed blast
qed


lemma no_shifts_to_mono:
  "G' \<subseteq> G \<Longrightarrow> \<nexists>v'. shifts_to G M u v v' \<pi> \<sigma> \<Longrightarrow> \<nexists>v'. shifts_to G' M u v v' \<pi> \<sigma>"
  by (auto dest: shifts_to_mono)
                                    
lemma remove_vertices_no_shifts_to_mono:
  "xs \<subseteq> xs' \<Longrightarrow> \<nexists>v'. shifts_to (G \<setminus> xs) M u v v' \<pi> \<sigma> \<Longrightarrow> \<nexists>u'. shifts_to (G \<setminus> xs') M u v v' \<pi> \<sigma>"
  by (auto dest: remove_vertices_inv_mono'[of xs xs' G] no_shifts_to_mono)

lemma shifts_to_matched_vertex_later_match:
  assumes "shifts_to G M u v v' \<pi> \<sigma>"
  assumes "{u,v} \<in> M"
  assumes "{u',v'} \<in> M"
  assumes "matching M"
  assumes  "u \<in> set \<pi>"
  shows "index \<pi> u < index \<pi> u'"
  using assms
  unfolding shifts_to_def
  apply auto
  by (metis doubleton_eq_iff index_eq_index_conv insertI1 linorder_neqE_nat matching_unique_match)

lemma remove_online_vertices_before_shifts_to_same:
  assumes "xs' \<subseteq> set \<pi>"
  assumes "xs \<subseteq> xs'"
  assumes "set \<sigma> \<inter> set \<pi> = {}"
  assumes "\<forall>x \<in> xs' - xs. index \<pi> x < index \<pi> u"
  assumes "shifts_to (G \<setminus> xs) M u v v' \<pi> \<sigma>"
  shows "shifts_to (G \<setminus> xs') M u v v' \<pi> \<sigma>"
  using assms
  unfolding shifts_to_def
  apply (auto dest: remove_vertices_inv_mono)
  by (smt (z3) DiffI Diff_disjoint Diff_insert_absorb disjoint_iff in_mono mem_Collect_eq nat_neq_iff remove_vertices_graph_def)

lemma remove_online_vertices_shifts_to_same:
  assumes "X \<subseteq> set \<pi>"
  assumes "u \<notin> X"
  assumes "set \<pi> \<inter> set \<sigma> = {}"
  assumes "matching M"
  assumes "(\<forall>x \<in> X. ((\<exists>v. {x,v} \<in> M) \<longrightarrow> index \<sigma> (THE v. {x,v} \<in> M) < index \<sigma> v))"
  assumes "shifts_to G M u v v' \<pi> \<sigma>"
  shows "shifts_to (G \<setminus> X) (M \<setminus> X) u v v' \<pi> \<sigma>"
  using assms
  unfolding shifts_to_def
  apply (auto dest: remove_vertices_subgraph')
   apply (metis Diff_disjoint Diff_insert_absorb Int_insert_left disjoint_iff in_remove_verticesI subset_eq)
  subgoal for v''
  proof -
    assume v'': "index \<sigma> v < index \<sigma> v''" "index \<sigma> v'' < index \<sigma> v'" "{u,v''} \<in> G \<setminus> X"
      and *: "\<forall>v''. index \<sigma> v < index \<sigma> v'' \<and> index \<sigma> v'' < index \<sigma> v' \<longrightarrow> {u, v''} \<in> G \<longrightarrow> (\<exists>u'. index \<pi> u' < index \<pi> u \<and> {u', v''} \<in> M)"

    then obtain u' where "index \<pi> u' < index \<pi> u" "{u',v''} \<in> M"
      by (auto dest: remove_vertices_subgraph')

    have "v'' \<notin> X"
      by (meson edges_are_Vs(2) remove_vertices_not_vs v''(3))

    from \<open>{u',v''} \<in> M\<close> \<open>matching M\<close> assms(5) \<open>index \<sigma> v < index \<sigma> v''\<close> have "u' \<notin> X"
      by (auto simp: the_match')

    with \<open>{u',v''} \<in> M\<close> \<open>v'' \<notin> X\<close> have "{u',v''} \<in> M \<setminus> X"
      by (auto intro: in_remove_verticesI)

    with \<open>index \<pi> u' < index \<pi> u\<close> show "\<exists>u'. index \<pi> u' < index \<pi> u \<and> {u',v''} \<in> M \<setminus> X"
      by blast
  qed
  done

lemma remove_vertices_in_diff: "{u,v} \<in> G \<setminus> X \<Longrightarrow> {u,v} \<notin> G \<setminus> X' \<Longrightarrow> u \<in> X' - X \<or> v \<in> X' - X"
  unfolding remove_vertices_graph_def
  by simp

lemma remove_offline_vertices_before_shifts_to_same:
  assumes "xs' \<subseteq> set \<sigma>"
  assumes "xs \<subseteq> xs'"
  assumes "set \<sigma> \<inter> set \<pi> = {}"
  assumes "\<forall>x \<in> xs' - xs. index \<sigma> x < index \<sigma> v"
  assumes "shifts_to (G \<setminus> xs) M u v v' \<pi> \<sigma>"
  shows "shifts_to (G \<setminus> xs') M u v v' \<pi> \<sigma>"
  using assms
  unfolding shifts_to_def
  apply (auto dest: remove_vertices_inv_mono)
  by (metis disjoint_iff index_conv_size_if_notin index_le_size leD not_less_iff_gr_or_eq remove_vertices_in_diff)

lemma remove_offline_vertices_before_shifts_to_same':
  assumes "X \<subseteq> set \<sigma>"
  assumes "set \<pi> \<inter> set \<sigma> = {}"
  assumes "\<forall>x \<in> X. index \<sigma> x < index \<sigma> v"
  assumes "shifts_to G M u v v' \<pi> \<sigma>"
  shows "shifts_to (G \<setminus> X) (M \<setminus> X) u v v' \<pi> \<sigma>"
  using assms
  unfolding shifts_to_def
  apply auto
    apply (metis Int_commute Int_insert_right_if0 disjoint_iff in_remove_verticesI inf_bot_right less_asym' subset_eq)
   apply (meson remove_vertices_subgraph')
  by (smt (verit, ccfv_threshold) Diff_disjoint Diff_insert_absorb Int_insert_left_if0 disjoint_iff in_remove_verticesI index_less_in_set less_asym' remove_vertices_subgraph')

lemma
  assumes "X \<subseteq> set \<pi>"
  assumes "bipartite M (set \<pi>) (set \<sigma>)"
  assumes "matching M"
  shows 
   remove_online_vertices_zig_zig_eq: "v \<in> set \<sigma> \<Longrightarrow>  \<forall>x \<in> X. ((\<exists>v'. {x,v'} \<in> M) \<longrightarrow> index \<sigma> (THE v'. {x,v'} \<in> M) < index \<sigma> v) \<Longrightarrow> zig (G \<setminus> X) (M \<setminus> X) v \<pi> \<sigma> = zig G M v \<pi> \<sigma>" and
   remove_online_vertices_zag_zag_eq: "u \<in> set \<pi> \<Longrightarrow> ((\<exists>v. {u,v} \<in> M \<Longrightarrow> \<forall>x \<in> X. ((\<exists>v. {x,v} \<in> M) \<longrightarrow> index \<sigma> (THE v. {x,v} \<in> M) < index \<sigma> (THE v. {u,v} \<in> M)))) \<Longrightarrow> zag (G \<setminus> X) (M \<setminus> X) u \<pi> \<sigma> = zag G M u \<pi> \<sigma>"
  using assms
proof (induction G M v \<pi> \<sigma> and G M u \<pi> \<sigma> rule: zig_zag.induct)
  case (1 M G v \<pi> \<sigma>)

  then have "matching (M \<setminus> X)"
    by (simp add: matching_remove_vertices)

  show ?case
  proof (cases "\<exists>u. {u,v} \<in> M")
    case True
    then obtain u where "{u,v} \<in> M" by blast
    with "1.hyps" have the_u: "(THE u. {u,v} \<in> M) = u"
      by (simp add: the_match)

    from \<open>{u,v} \<in> M\<close> \<open>bipartite M (set \<pi>) (set \<sigma>)\<close> \<open>v \<in> set \<sigma>\<close> have "u \<in> set \<pi>"
      by (smt (verit, ccfv_SIG) DiffD2 Diff_insert_absorb bipartite_disjointD bipartite_edgeE disjoint_iff_not_equal insertE insertI1)

    have "u \<notin> X"
      using "1"(4) \<open>matching M\<close> \<open>{u,v} \<in> M\<close>
      by (auto simp: the_match')

    have "v \<notin> X"
      using "1.prems" bipartite_disjointD by blast

    with \<open>{u,v} \<in> M\<close> \<open>u \<notin> X\<close> have "{u,v} \<in> M \<setminus> X"
      by (auto intro: in_remove_verticesI)

    with \<open>matching (M \<setminus> X)\<close> have the_u_X: "(THE u. {u,v} \<in> M \<setminus> X) = u"
      by (simp add: the_match)

    have "\<forall>x\<in>X. (\<exists>v. {x, v} \<in> M) \<longrightarrow> index \<sigma> (THE v. {x, v} \<in> M) < index \<sigma> (THE v. {u, v} \<in> M)"
      using "1"(4) \<open>{u,v} \<in> M\<close> \<open>matching M\<close>
      by (simp add: the_match')
    
    with 1 True the_u the_u_X \<open>matching (M \<setminus> X)\<close> \<open>{u,v} \<in> M \<setminus> X\<close> \<open>u \<in> set \<pi>\<close> show ?thesis
      by (auto simp: zig.simps)
  next
    case False
    then have "\<nexists>u. {u,v} \<in> M \<setminus> X"
      using remove_vertices_subgraph by blast
    with \<open>matching M\<close> False \<open>matching (M \<setminus> X)\<close> show ?thesis 
      by (simp add: zig.simps)
  qed
next
  case (3 M G u \<pi> \<sigma>)

  then have "matching (M \<setminus> X)"
    by (simp add: matching_remove_vertices)

  consider (match) "\<exists>v. {u,v} \<in> M" | (no_match) "\<nexists>v. {u,v} \<in> M" by blast

  then show ?case
  proof cases
    case match
    then obtain v where "{u,v} \<in> M" by blast
    with "3.hyps" have the_v: "(THE v. {u,v} \<in> M) = v"
      by (simp add: the_match')

    have "v \<notin> X"
      by (smt (verit, ccfv_SIG) "3.prems"(1) "3.prems"(3) "3.prems"(4) IntI \<open>{u, v} \<in> M\<close> bipartite_disjointD bipartite_edgeE doubleton_eq_iff empty_iff subset_iff)

    have "u \<notin> X"
      using "3"(4) \<open>{u, v} \<in> M\<close> by blast

    with \<open>{u,v} \<in> M\<close> \<open>v \<notin> X\<close> have "{u,v} \<in> M \<setminus> X"
      by (auto intro: in_remove_verticesI)

    with \<open>matching (M \<setminus> X)\<close> have the_v_X: "(THE v. {u,v} \<in> M \<setminus> X) = v"
      by (simp add: the_match')

    show ?thesis
    proof (cases "\<exists>v'. shifts_to G M u v v' \<pi> \<sigma>")
      case True
      then obtain v' where shift_v': "shifts_to G M u v v' \<pi> \<sigma>" by blast
      then have the_v': "(THE v'. shifts_to G M u v v' \<pi> \<sigma>) = v'"
        by (simp add: the_shifts_to)

      from shift_v' \<open>X \<subseteq> set \<pi>\<close> \<open>u \<notin> X\<close> \<open>bipartite M (set \<pi>) (set \<sigma>)\<close> \<open>matching M\<close>
      have shift_v'_X: "shifts_to (G \<setminus> X) (M \<setminus> X) u v v' \<pi> \<sigma>"
        apply (auto intro!: remove_online_vertices_shifts_to_same dest: bipartite_disjointD)
        using "3.prems"(2) \<open>{u, v} \<in> M\<close> the_v by blast

      then have the_v'_X: "(THE v'. shifts_to (G \<setminus> X) (M \<setminus> X) u v v' \<pi> \<sigma>) = v'"
        by (simp add: the_shifts_to)


      with 3 match the_v shift_v' the_v' the_v_X shift_v'_X the_v'_X \<open>matching (M \<setminus> X)\<close> \<open>{u,v} \<in> M \<setminus> X\<close> show ?thesis
        apply (auto simp: zag.simps)
        by (meson order.strict_trans shifts_to_def)
        
    next
      case False

      with "3"(4)[OF match] \<open>bipartite M (set \<pi>) (set \<sigma>)\<close> \<open>X \<subseteq> set \<pi>\<close> False have "\<nexists>v'. shifts_to (G \<setminus> X) (M \<setminus> X) u v v' \<pi> \<sigma>"
        using remove_online_vertices_before_shifts_to_mono[OF bipartite_disjointD[OF \<open>bipartite M (set \<pi>) (set \<sigma>)\<close>] \<open>X \<subseteq> set \<pi>\<close> \<open>matching M\<close> "3"(4)[OF match], simplified the_v]
        by (fastforce dest: bipartite_disjointD)

      with \<open>matching M\<close> False match the_v \<open>matching (M \<setminus> X)\<close> \<open>{u,v} \<in> M \<setminus> X\<close> the_v_X show ?thesis
        by (simp add: zag.simps)
    qed
  next
    case no_match
    then have "\<nexists>v. {u,v} \<in> M \<setminus> X"
      using remove_vertices_subgraph by blast

    with \<open>matching M\<close> \<open>matching (M \<setminus> X)\<close> no_match show ?thesis 
      by (simp add: zag.simps)
  qed
qed blast+

lemma
  assumes "X \<subseteq> set \<sigma>"
  assumes "matching M"
  assumes "bipartite M (set \<pi>) (set \<sigma>)"
  shows
    remove_offline_vertices_zig_zig_eq: "v \<in> set \<sigma> \<Longrightarrow> (\<forall>x \<in> X. index \<sigma> x < index \<sigma> v) \<Longrightarrow> zig (G \<setminus> X) (M \<setminus> X) v \<pi> \<sigma> = zig G M v \<pi> \<sigma>" and
    remove_offline_vertices_zag_zag_eq: "u \<in> set \<pi> \<Longrightarrow> (\<exists>v. {u,v} \<in> M \<Longrightarrow> \<forall>x \<in> X. index \<sigma> x < index \<sigma> (THE v. {u,v} \<in> M)) \<Longrightarrow> zag (G \<setminus> X) (M \<setminus> X) u \<pi> \<sigma> = zag G M u \<pi> \<sigma>"
  using assms
proof (induction G M v \<pi> \<sigma> and G M u \<pi> \<sigma> rule: zig_zag.induct)
  case (1 M G v \<pi> \<sigma>)

  then have "matching (M \<setminus> X)"
    by (simp add: matching_remove_vertices)

  show ?case
  proof (cases "\<exists>u. {u,v} \<in> M")
    case True
    then obtain u where "{u,v} \<in> M" by blast
    with \<open>matching M\<close> have the_u: "(THE u. {u,v} \<in> M) = u"
      by (simp add: the_match)

    from \<open>v \<in> set \<sigma>\<close> \<open>\<forall>x\<in>X. index \<sigma> x < index \<sigma> v\<close> have "v \<notin> X" by blast

    from \<open>v \<in> set \<sigma>\<close> \<open>{u,v} \<in> M\<close> \<open>bipartite M (set \<pi>) (set \<sigma>)\<close> have "u \<in> set \<pi>"
      unfolding bipartite_def
      by fast

    then have "u \<notin> X"
      by (metis \<open>X \<subseteq> set \<sigma>\<close> \<open>bipartite M (set \<pi>) (set \<sigma>)\<close> IntI bipartite_disjointD empty_iff in_mono)

    with \<open>{u,v} \<in> M\<close> \<open>v \<notin> X\<close> have "{u,v} \<in> M \<setminus> X"
      by (auto intro: in_remove_verticesI)

    with \<open>matching (M \<setminus> X)\<close> have the_u': "(THE u. {u,v} \<in> M \<setminus> X) = u"
      by (simp add: the_match)

    with 1 True \<open>{u,v} \<in> M\<close> the_u \<open>matching (M \<setminus> X)\<close> \<open>{u,v} \<in> M \<setminus> X\<close> the_u' \<open>u \<in> set \<pi>\<close> show ?thesis
      by (auto simp: zig.simps simp: the_match')
  next
    case False

    then have "\<nexists>u. {u,v} \<in> M \<setminus> X"
      using remove_vertices_subgraph by blast

    with False \<open>matching M\<close> \<open>matching (M \<setminus> X)\<close> show ?thesis
      by (auto simp: zig.simps)
  qed
next
  case (3 M G u \<pi> \<sigma>)

  then have "matching (M \<setminus> X)"
    by (simp add: matching_remove_vertices)

  consider (match) "\<exists>v. {u,v} \<in> M" | (no_match) "\<nexists>v. {u,v} \<in> M" by blast
  then show ?case 
  proof (cases)
    case match
    then obtain v where "{u,v} \<in> M" by blast
    with \<open>matching M\<close> have the_v: "(THE v. {u,v} \<in> M) = v"
      by (simp add: the_match')

    from \<open>u \<in> set \<pi>\<close> have "u \<notin> X"
      using \<open>X \<subseteq> set \<sigma>\<close> \<open>bipartite M (set \<pi>) (set \<sigma>)\<close> bipartite_disjointD by blast

    from \<open>u \<in> set \<pi>\<close> \<open>{u,v} \<in> M\<close> \<open>bipartite M (set \<pi>) (set \<sigma>)\<close> have "v \<in> set \<sigma>"
      by (smt (verit, ccfv_SIG) bipartite_disjointD bipartite_edgeE disjoint_iff_not_equal doubleton_eq_iff)

    from \<open>\<exists>v. {u, v} \<in> M \<Longrightarrow> \<forall>x\<in>X. index \<sigma> x < index \<sigma> (THE v. {u, v} \<in> M)\<close> match the_v have "v \<notin> X"
      by blast

    with \<open>{u,v} \<in> M\<close> \<open>u \<notin> X\<close> have "{u,v} \<in> M \<setminus> X"
      by (auto intro: in_remove_verticesI)

    with \<open>matching (M \<setminus> X)\<close> have the_v_X: "(THE v. {u,v} \<in> M \<setminus> X) = v"
      by (simp add: the_match')


    show ?thesis
    proof (cases "\<exists>v'. shifts_to G M u v v' \<pi> \<sigma>")
      case True
      then obtain v' where v_shifts_to_v': "shifts_to G M u v v' \<pi> \<sigma>" by blast
      then have the_v': "(THE v'. shifts_to G M u v v' \<pi> \<sigma>) = v'"
        by (simp add: the_shifts_to)

      with v_shifts_to_v' "3.prems" have v_shifts_to_v'_X: "shifts_to (G \<setminus> X) (M \<setminus> X) u v v' \<pi> \<sigma>"
        by (metis bipartite_disjointD match remove_offline_vertices_before_shifts_to_same' the_v)

      then have the_v'_X: "(THE v'. shifts_to (G \<setminus> X) (M \<setminus> X) u v v' \<pi> \<sigma>) = v'"
        by (simp add: the_shifts_to)

      have "\<forall>x\<in>X. index \<sigma> x < index \<sigma> v'"
        by (metis "3.prems"(2) match order.strict_trans shifts_to_def the_v v_shifts_to_v'_X)


      with 3 match the_v True the_v' \<open>matching (M \<setminus> X)\<close> \<open>{u,v} \<in> M \<setminus> X\<close> the_v_X the_v'_X v_shifts_to_v'_X
      show ?thesis
        by (auto simp: zag.simps dest: shifts_to_only_from_input)
    next
      case False

      then have "\<nexists>v'. shifts_to (G \<setminus> X) (M \<setminus> X) u v v' \<pi> \<sigma>"
        by (metis "3.prems"(2) "3.prems"(3) "3.prems"(5) bipartite_disjointD match remove_offline_vertices_before_shifts_to_mono the_v)

      with \<open>matching M\<close> False match the_v \<open>matching (M \<setminus> X)\<close> \<open>{u,v} \<in> M \<setminus> X\<close> the_v_X show ?thesis
        by (auto simp: zag.simps)
    qed
  next
    case no_match
    then have "\<nexists>v. {u,v} \<in> M \<setminus> X"
      using remove_vertices_subgraph by blast

    with \<open>matching M\<close> no_match \<open>matching (M \<setminus> X)\<close> show ?thesis
      by (simp add: zag.simps)
  qed
qed blast+


lemma ranking_matching_shifts_to_reduced_edges:
  assumes rm_M: "ranking_matching G M \<pi> \<sigma>"
  assumes "ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>"
  assumes "x \<in> set \<sigma>"
  assumes "{u,x} \<in> M"
  assumes "{u,x'} \<in> M'"
  shows "shifts_to G M u x x' \<pi> \<sigma>"
proof -
  have disjoint: "set \<pi> \<inter> set \<sigma> = {}" using rm_M
    by (auto dest: ranking_matchingD bipartite_disjointD)

  have "u \<in> set \<pi>" using \<open>x \<in> set \<sigma>\<close> \<open>{u,x} \<in> M\<close> rm_M
    by (auto intro: ranking_matching_bipartite_edges')

  have "x \<notin> Vs M'" using \<open>ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>\<close>
    by (auto dest!: ranking_matchingD Vs_subset simp: remove_vertices_not_vs)

  then have "x \<noteq> x'"
    using assms(5) insert_commute by auto

  have rm_M': "ranking_matching (G \<setminus> {x}) M' \<pi> \<sigma>"
    using \<open>ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>\<close> ranking_matching_commute
    by blast

  have "{u,x'} \<in> G"
    using \<open>{u,x'} \<in> M'\<close> rm_M' ranking_matchingD remove_vertices_subgraph by blast

  have no_u'_for_x': "\<nexists>u'. index \<pi> u' < index \<pi> u \<and> {u',x'} \<in> M"
  proof (rule ccontr, simp)
    assume "\<exists>u'. index \<pi> u' < index \<pi> u \<and> {u',x'} \<in> M"
    then obtain u' where earlier_match: "index \<pi> u' < index \<pi> u" "{u',x'} \<in> M" by blast

    with rm_M rm_M' \<open>{u,x'} \<in> M'\<close> \<open>x \<noteq> x'\<close>
    show False
    proof (induction "index \<pi> u'" arbitrary: u u' x' rule: less_induct)
      case less
      then have "{u',x'} \<in> G"
        by (auto dest: ranking_matchingD)

      with \<open>x \<noteq> x'\<close> have "{u',x'} \<in> G \<setminus> {x}"
        by (metis Int_empty_right assms(3) disjoint disjoint_iff in_remove_verticesI index_conv_size_if_notin index_less_size_conv insert_iff less.prems(5) not_less_iff_gr_or_eq)

      with less.prems obtain x'' where earlier_match: "{u',x''} \<in> M'" "index \<sigma> x'' < index \<sigma> x'"
        by (auto elim: ranking_matching_earlier_match_offlineE)

      with less.prems have "{u',x''} \<in> G"
        using ranking_matchingD remove_vertices_subgraph' by blast

      with earlier_match less.prems obtain u'' where u'': "{u'',x''} \<in> M" "index \<pi> u'' < index \<pi> u'"
        by (auto elim: ranking_matching_earlier_match_onlineE)

      then have "x \<noteq> x''"
        using \<open>x \<notin> Vs M'\<close> earlier_match insert_commute by blast

      with u'' less.prems \<open>{u',x''} \<in> M'\<close> show ?case
        by (auto intro: less.hyps)
    qed
  qed

  show ?thesis
    unfolding shifts_to_def
  proof (intro conjI)
    show \<open>u \<in> set \<pi>\<close> using \<open>u \<in> set \<pi>\<close> by blast
  next
    show "x' \<in> set \<sigma>" using \<open>u \<in> set \<pi>\<close> \<open>{u,x'} \<in> G\<close> rm_M disjoint
      by (auto dest: ranking_matchingD elim!: bipartite_edgeE)
  next
    show "index \<sigma> x < index \<sigma> x'"
    proof (rule ccontr)
      assume "\<not> index \<sigma> x < index \<sigma> x'"
      with \<open>x \<noteq> x'\<close> \<open>x \<in> set \<sigma>\<close> index_eq_index_conv have "index \<sigma> x' < index \<sigma> x"
        by fastforce

      with rm_M \<open>{u,x} \<in> M\<close> \<open>{u,x'} \<in> G\<close> have "\<exists>u'. {u',x'} \<in> M \<and> index \<pi> u' < index \<pi> u"
        unfolding ranking_matching_def
        by blast

      with no_u'_for_x' show False by blast
    qed
  next
    show "{u,x'} \<in> G" using \<open>{u,x'} \<in> G\<close> by blast
  next
    show "\<nexists>u'. index \<pi> u' < index \<pi> u \<and> {u',x'} \<in> M" using no_u'_for_x' by blast
  next
    show "\<forall>x''. index \<sigma> x < index \<sigma> x'' \<and> index \<sigma> x'' < index \<sigma> x' \<longrightarrow>
      {u,x''} \<notin> G \<or> (\<exists>u'. index \<pi> u' < index \<pi> u \<and> {u',x''} \<in> M)"
    proof (rule ccontr, simp)
      assume "\<exists>x''. index \<sigma> x < index \<sigma> x'' \<and> index \<sigma> x'' < index \<sigma> x' \<and> {u,x''} \<in> G \<and> (\<forall>u'. index \<pi> u' < index \<pi> u \<longrightarrow> {u',x''} \<notin> M)"
      then obtain x'' where x'': "index \<sigma> x < index \<sigma> x''" "index \<sigma> x'' < index \<sigma> x'" "{u,x''} \<in> G"
        and no_earlier_u_for_x'': "\<forall>u'. index \<pi> u' < index \<pi> u \<longrightarrow> {u',x''} \<notin> M"
        by blast

      then have "{u,x''} \<in> G \<setminus> {x}"
        by (metis \<open>u \<in> set \<pi>\<close> assms(3) disjoint disjoint_iff_not_equal empty_iff in_remove_verticesI insertE neq_iff)

      from \<open>index \<sigma> x < index \<sigma> x''\<close> have "x \<noteq> x''"
        by blast

      with rm_M' \<open>{u,x'} \<in> M'\<close> \<open>{u,x''} \<in> G \<setminus> {x}\<close> \<open>index \<sigma> x'' < index \<sigma> x'\<close>
      obtain u' where "{u',x''} \<in> M'" "index \<pi> u' < index \<pi> u"
        by (auto elim: ranking_matching_earlier_match_onlineE)

      with rm_M' have "{u',x''} \<in> G"
        by (auto dest: ranking_matchingD remove_vertices_subgraph')

      have "u \<noteq> u'"
        using \<open>index \<pi> u' < index \<pi> u\<close> by blast

      from \<open>index \<pi> u' < index \<pi> u\<close> have "u' \<in> set \<pi>"
        using index_less_in_set by fast

      show False
      proof (cases "\<exists>u''. {u'',x''} \<in> M")
        case True
        then obtain u'' where "{u'',x''} \<in> M" by blast
        with x'' \<open>{u,x} \<in> M\<close> \<open>x \<noteq> x''\<close> rm_M have "u'' \<noteq> u"
          by (auto dest: ranking_matching_unique_match)
                                      
        with no_earlier_u_for_x'' \<open>{u'',x''} \<in> M\<close> have "index \<pi> u < index \<pi> u''"
          by (meson \<open>u \<in> set \<pi>\<close> index_eq_index_conv less_linear)

        with \<open>index \<pi> u' < index \<pi> u\<close> have "index \<pi> u' < index \<pi> u''" by linarith

        with \<open>{u'',x''} \<in> M\<close> \<open>{u',x''} \<in> G\<close> rm_M
        obtain x3 where x3: "{u',x3} \<in> M" "index \<sigma> x3 < index \<sigma> x''"
          by (auto elim: ranking_matching_earlier_match_offlineE)

        then have "x3 \<in> set \<sigma>"
          by (auto dest: index_less_in_set)

        with x3 \<open>u' \<in> set \<pi>\<close> \<open>{u',x''} \<in> M'\<close> \<open>index \<pi> u' < index \<pi> u\<close>
        show ?thesis
        proof (induction "index \<sigma> x3" arbitrary: x3 u' x'' rule: less_induct)
          case (less s p)

          have "p \<noteq> u" using \<open>index \<pi> p < index \<pi> u\<close> by blast

          have "p \<noteq> x"
            using \<open>x \<in> set \<sigma>\<close> disjoint \<open>p \<in> set \<pi>\<close> by blast

          with \<open>p \<noteq> u\<close> \<open>{u,x} \<in> M\<close> \<open>{p,s} \<in> M\<close> \<open>index \<pi> p < index \<pi> u\<close> rm_M have "s \<noteq> x"
            by (auto dest: ranking_matching_unique_match')

          with less \<open>p \<noteq> x\<close> \<open>x \<notin> Vs M'\<close> rm_M have "{p,s} \<in> G \<setminus> {x}"
            by (auto intro!: in_remove_verticesI dest: ranking_matchingD)

          with less rm_M' obtain p' where p': "{p',s} \<in> M'" "index \<pi> p' < index \<pi> p"
            by (auto elim: ranking_matching_earlier_match_onlineE)

          with \<open>index \<pi> p < index \<pi> u\<close> have \<open>index \<pi> p' < index \<pi> u\<close> by linarith

          with index_less_in_set have "p' \<in> set \<pi>" by fast

          from p' rm_M' have "{p',s} \<in> G"
            by (auto dest: ranking_matchingD remove_vertices_subgraph')

          with \<open>{p,s} \<in> M\<close> \<open>index \<pi> p' < index \<pi> p\<close> rm_M
          obtain s' where "{p',s'} \<in> M" "index \<sigma> s' < index \<sigma> s"
            by (auto elim: ranking_matching_earlier_match_offlineE)

          with index_less_in_set have "s' \<in> set \<sigma>" by fast

          with less \<open>index \<sigma> s' < index \<sigma> s\<close> \<open>{p',s'} \<in> M\<close> \<open>p' \<in> set \<pi>\<close>
            \<open>{p',s} \<in> M'\<close> \<open>index \<pi> p' < index \<pi> u\<close> \<open>s' \<in> set \<sigma>\<close>
          show ?case
            by auto
        qed
      next
        case False
        then show ?thesis
        proof (cases "\<exists>x3. {u',x3} \<in> M")
          case True
          then obtain x3 where x3: "{u',x3} \<in> M" by blast

          with \<open>index \<pi> u' < index \<pi> u\<close> \<open>u \<noteq> u'\<close> rm_M \<open>{u,x} \<in> M\<close> have "x \<noteq> x3"
            by (auto dest: ranking_matching_unique_match')

          consider (before_x'') "index \<sigma> x3 < index \<sigma> x''" | (x'') "index \<sigma> x3 = index \<sigma> x''" | (after_x'') "index \<sigma> x'' < index \<sigma> x3"
            by linarith

          then show ?thesis
          proof cases
            case before_x''
            with x3 \<open>{u',x''} \<in> M'\<close> \<open>x \<noteq> x3\<close> \<open>u' \<in> set \<pi>\<close> \<open>index \<pi> u' < index \<pi> u\<close> show ?thesis
            proof (induction "index \<sigma> x3" arbitrary: x3 u' x'' rule: less_induct)
              case (less s p)
              with rm_M \<open>x \<in> set \<sigma>\<close> disjoint have "{p,s} \<in> G \<setminus> {x}"
                by (auto intro: in_remove_verticesI dest: ranking_matchingD)

              with less rm_M'
              obtain p' where p': "{p',s} \<in> M'" "index \<pi> p' < index \<pi> p"
                by (auto elim: ranking_matching_earlier_match_onlineE)

              then have "p' \<in> set \<pi>" by (auto intro: index_less_in_set)

              from p' \<open>index \<pi> p < index \<pi> u\<close> have "index \<pi> p' < index \<pi> u" by linarith

              from p' rm_M' have "{p',s} \<in> G"
                by (auto dest: ranking_matchingD remove_vertices_subgraph')

              with rm_M \<open>{p,s} \<in> M\<close> \<open>index \<pi> p' < index \<pi> p\<close>
              obtain s' where "{p',s'} \<in> M" "index \<sigma> s' < index \<sigma> s"
                by (auto elim: ranking_matching_earlier_match_offlineE)

              have "u \<noteq> p'"
                using \<open>index \<pi> p' < index \<pi> p\<close> less.prems(5) less_asym' by blast

              with rm_M \<open>index \<pi> p' < index \<pi> u\<close> \<open>{u,x} \<in> M\<close> \<open>{p',s'} \<in> M\<close> have "x \<noteq> s'"
                by (auto dest:  ranking_matching_unique_match')

              with less \<open>index \<sigma> s' < index \<sigma> s\<close> \<open>{p',s'} \<in> M\<close> \<open>{p',s} \<in> M'\<close> \<open>x \<noteq> s'\<close> \<open>p' \<in> set \<pi>\<close>
                \<open>index \<pi> p' < index \<pi> u\<close>
              show ?case
                by auto
            qed
          next
            case x''
            then show ?thesis
              by (metis False \<open>index \<sigma> x'' < index \<sigma> x'\<close> \<open>{u', x3} \<in> M\<close> index_eq_index_conv index_less_in_set)
          next
            case after_x''
            then show ?thesis
              by (meson \<open>index \<pi> u' < index \<pi> u\<close> \<open>{u', x''} \<in> G\<close> \<open>{u', x3} \<in> M\<close> assms(1) less_le_trans less_or_eq_imp_le no_earlier_u_for_x'' ranking_matching_earlier_match_onlineE)
          qed
        next
          case False
          with \<open>\<nexists>u''. {u'', x''} \<in> M\<close> rm_M have "u' \<notin> Vs M" "x'' \<notin> Vs M"
            by (auto dest: ranking_matchingD simp: graph_abs_no_edge_no_vertex insert_commute)

          with \<open>{u',x''} \<in> G\<close> rm_M show ?thesis
            by (auto dest: ranking_matchingD maximal_matching_edgeD)
        qed
      qed
    qed
  qed
qed

lemma ranking_matching_shifts_to_original_edges:
  assumes rm_G: "ranking_matching G M \<pi> \<sigma>"
  assumes "ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>"
  assumes "x \<in> set \<sigma>"
  assumes "{u,x} \<in> M"
  assumes "{u,x'} \<in> M'"
  assumes "{u',x'} \<in> M"
  assumes u_before_u': "index \<pi> u < index \<pi> u'"
  shows "shifts_to (G \<setminus> {x}) M' x' u u' \<sigma> \<pi>"
  using assms
proof -
  have rm_G': "ranking_matching (G \<setminus> {x}) M' \<pi> \<sigma>" using \<open>ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>\<close>
    by (auto dest: ranking_matching_commute)

  have disjoint: "set \<pi> \<inter> set \<sigma> = {}" using \<open>ranking_matching G M \<pi> \<sigma>\<close>
    by (auto dest: ranking_matchingD bipartite_disjointD)

  have "u \<in> set \<pi>" using u_before_u' by (auto intro: index_less_in_set)
  have "x' \<in> set \<sigma>"
    using assms
    by (auto dest: ranking_matching_shifts_to_reduced_edges shifts_to_only_from_input)

  with rm_G \<open>{u',x'} \<in> M\<close> have "u' \<in> set \<pi>"
    by (auto intro: ranking_matching_bipartite_edges')

  with disjoint \<open>x \<in> set \<sigma>\<close> have "x \<noteq> u'" by blast

  from assms have "x \<noteq> x'"
    by (auto dest: ranking_matching_unique_match')

  have "u' \<noteq> u"
    using u_before_u' by blast

  have "{u',x'} \<in> G"
    using assms
    by (auto dest: ranking_matchingD)

  show ?thesis
    unfolding shifts_to_def
  proof (intro conjI)
    show "x' \<in> set \<sigma>" using \<open>x' \<in> set \<sigma>\<close> by blast
  next
    show "u' \<in> set \<pi>" using \<open>u' \<in> set \<pi>\<close> by blast
  next
    show "index \<pi> u < index \<pi> u'" using assms by blast
  next
    from \<open>x \<noteq> x'\<close> \<open>x \<noteq> u'\<close> \<open>{u',x'} \<in> G\<close> show "{x',u'} \<in> G \<setminus> {x}" 
      by (auto intro!: in_remove_verticesI simp: insert_commute)
  next
    show "\<nexists>x''. index \<sigma> x'' < index \<sigma> x' \<and> {x'',u'} \<in> M'"
    proof (rule ccontr, simp)
      assume "\<exists>x''. index \<sigma> x'' < index \<sigma> x' \<and> {x'',u'} \<in> M'"
      then obtain x'' where "index \<sigma> x'' < index \<sigma> x'" "{u',x''} \<in> M'"
        by (auto simp: insert_commute)

      with \<open>{u',x'} \<in> M\<close> show False
      proof (induction "index \<sigma> x''" arbitrary: x'' u' x' rule: less_induct)
        case less
        with rm_G' have "{u',x''} \<in> G"
          by (auto dest: ranking_matchingD remove_vertices_subgraph')

        with less rm_G \<open>{u',x'} \<in> M\<close>
        obtain u'' where u'': "index \<pi> u'' < index \<pi> u'" "{u'',x''} \<in> M"
          by (auto elim: ranking_matching_earlier_match_onlineE)

        with \<open>x \<in> set \<sigma>\<close> disjoint have "u'' \<noteq> x"
          by (auto dest!: index_less_in_set)

        from rm_G' \<open>{u', x''} \<in> M'\<close> have "x \<noteq> x''"
          by (metis in_mono insertI1 insert_commute ranking_matchingD remove_vertices_not_vs vs_member_intro)

        with \<open>{u'',x''} \<in> M\<close> \<open>u'' \<noteq> x\<close> rm_G have "{u'',x''} \<in> G \<setminus> {x}" 
          by (auto intro: in_remove_verticesI dest: ranking_matchingD)

        with less u'' rm_G'
        obtain x3 where "index \<sigma> x3 < index \<sigma> x''" "{u'',x3} \<in> M'"                          
          by (auto elim: ranking_matching_earlier_match_offlineE)

        with less \<open>{u'',x''} \<in> M\<close> show ?case
          by auto
      qed
    qed
  next
    show "\<forall>u''. index \<pi> u < index \<pi> u'' \<and> index \<pi> u'' < index \<pi> u' \<longrightarrow> 
      {x',u''} \<notin> G \<setminus> {x} \<or> (\<exists>x''. index \<sigma> x'' < index \<sigma> x' \<and> {x'',u''} \<in> M')"
    proof (rule ccontr, simp)
      assume "\<exists>u''. index \<pi> u < index \<pi> u'' \<and> index \<pi> u'' < index \<pi> u' \<and> {x', u''} \<in> G \<setminus> {x} \<and> 
        (\<forall>x''. index \<sigma> x'' < index \<sigma> x' \<longrightarrow> {x'', u''} \<notin> M')"

      then obtain u'' where u'': "index \<pi> u < index \<pi> u''" "index \<pi> u'' < index \<pi> u'" "{u'',x'} \<in> G \<setminus> {x}"
        and no_x''_before_x'_for_u'': "\<nexists>x''. index \<sigma> x'' < index \<sigma> x' \<and> {u'',x''} \<in> M'"
        by (auto simp: insert_commute)

      then have "u \<noteq> u''"
        by blast

      with u'' rm_G \<open>{u',x'} \<in> M\<close>
      obtain x'' where x'': "{u'',x''} \<in> M" "index \<sigma> x'' < index \<sigma> x'"
        by (auto elim: ranking_matching_earlier_match_offlineE dest: remove_vertices_subgraph')

      from rm_G u'' x'' \<open>{u,x} \<in> M\<close> have "x \<noteq> x''"
        by (auto dest: ranking_matching_unique_match')

      from x'' no_x''_before_x'_for_u'' have "{u'',x''} \<notin> M'" by blast

      with x'' \<open>u \<noteq> u''\<close> \<open>x \<noteq> x''\<close> show False
      proof (induction "index \<sigma> x''" arbitrary: x'' u'' rule: less_induct)
        case less

        with rm_G have "{u'',x''} \<in> G \<setminus> {x}"
          apply (auto intro!: in_remove_verticesI dest: ranking_matchingD)
          by (metis assms(3) disjoint disjoint_iff index_less_in_set ranking_matching_bipartite_edges ranking_matching_commute)

        then show ?case
        proof (cases "\<exists>x3. {u'',x3} \<in> M'")
          case True
          then obtain x3 where "{u'',x3} \<in> M'" by blast
          with \<open>{u'',x''} \<notin> M'\<close> consider (before_x'') "index \<sigma> x3 < index \<sigma> x''" | (after_x'') "index \<sigma> x'' < index \<sigma> x3"

            by (metis index_eq_index_conv index_less_in_set less.prems(2) linorder_neqE_nat)

          then show ?thesis
          proof cases
            case before_x''
            from \<open>{u'',x3} \<in> M'\<close> rm_G' have "{u'',x3} \<in> G"
              by (auto dest: ranking_matchingD remove_vertices_subgraph')

            with before_x'' rm_G \<open>{u'',x''} \<in> M\<close> obtain u3 where "{u3,x3} \<in> M" "index \<pi> u3 < index \<pi> u''"
              by (auto elim: ranking_matching_earlier_match_onlineE)

            have "x \<noteq> x3"
              by (metis \<open>{u'', x3} \<in> M'\<close> edges_are_Vs insert_commute ranking_matchingD remove_vertices_not_vs rm_G' singletonI subset_iff)

            with rm_G \<open>{u3,x3} \<in> M\<close> \<open>{u,x} \<in> M\<close> have "u \<noteq> u3"
              by (metis ranking_matching_def the_match')

            from rm_G' \<open>{u'',x3} \<in> M'\<close> \<open>index \<pi> u3 < index \<pi> u''\<close> have "{u3,x3} \<notin> M'"
              by (auto dest: ranking_matching_unique_match')


            with less before_x'' \<open>{u3,x3} \<in> M\<close> \<open>u \<noteq> u3\<close> \<open>x \<noteq> x3\<close> show ?thesis 
              by auto
          next
            case after_x''

            with rm_G' \<open>{u'',x3} \<in> M'\<close> \<open>{u'',x''} \<in> G \<setminus> {x}\<close> obtain u3 where "{u3,x''} \<in> M'" "index \<pi> u3 < index \<pi> u''"
              by (auto elim: ranking_matching_earlier_match_onlineE)

            with rm_G' have "{u3,x''} \<in> G" 
              by (auto dest: ranking_matchingD remove_vertices_subgraph')

            with rm_G \<open>{u'',x''} \<in> M\<close> \<open>index \<pi> u3 < index \<pi> u''\<close> obtain x4 where "{u3,x4} \<in> M" "index \<sigma> x4 < index \<sigma> x''"
              by (auto elim: ranking_matching_earlier_match_offlineE)

            have "x \<noteq> x4"
              by (metis (no_types, lifting) \<open>{u3, x''} \<in> M'\<close> \<open>{u3, x4} \<in> M\<close> assms(4) assms(5) less.prems(2) neq_iff ranking_matching_def rm_G rm_G' the_match the_match')

            with rm_G' \<open>{u3,x''} \<in> M'\<close> \<open>{u,x'} \<in> M'\<close> \<open>index \<sigma> x'' < index \<sigma> x'\<close> have "u \<noteq> u3"
              by (auto dest: ranking_matching_unique_match)

            from rm_G' \<open>{u3,x''} \<in> M'\<close> \<open>index \<sigma> x4 < index \<sigma> x''\<close> have "{u3,x4} \<notin> M'"
              by (auto dest: ranking_matching_unique_match)

            with less \<open>index \<sigma> x4 < index \<sigma> x''\<close> \<open>{u3,x4} \<in> M\<close> \<open>u \<noteq> u3\<close> \<open>x \<noteq> x4\<close> show ?thesis
              by auto
          qed
        next
          case False
          with rm_G' have "u'' \<notin> Vs M'"
            by (intro graph_abs_no_edge_no_vertex) (auto dest: ranking_matchingD graph_abs_subgraph)

          with rm_G' \<open>{u'',x''} \<in> G \<setminus> {x}\<close> obtain u3 where "{u3,x''} \<in> M'"
            unfolding ranking_matching_def
            by (metis graph_abs_no_edge_no_vertex insert_commute maximal_matching_def ranking_matchingD rm_G')

          with rm_G' have "index \<pi> u3 < index \<pi> u''"
            by (smt (verit, ccfv_SIG) \<open>u'' \<notin> Vs M'\<close> \<open>{u'', x''} \<in> G \<setminus> {x}\<close> edges_are_Vs index_eq_index_conv index_less_in_set less.prems(2) not_less_iff_gr_or_eq ranking_matching_bipartite_edges' ranking_matching_def)

          from rm_G' \<open>{u3,x''} \<in> M'\<close> have "{u3,x''} \<in> G" 
            by (auto dest: ranking_matchingD remove_vertices_subgraph')

          with rm_G \<open>{u'',x''} \<in> M\<close> \<open>index \<pi> u3 < index \<pi> u''\<close> obtain x3 where x3: "{u3,x3} \<in> M" "index \<sigma> x3 < index \<sigma> x''"
            by (auto elim: ranking_matching_earlier_match_offlineE)

          from rm_G' \<open>{u,x'} \<in> M'\<close> \<open>index \<sigma> x'' < index \<sigma> x'\<close> \<open>{u3, x''} \<in> M'\<close> have "u \<noteq> u3"
            by (auto dest: ranking_matching_unique_match)

          then have "x \<noteq> x3"
            by (metis assms(4) ranking_matching_def rm_G the_match x3(1))

          from rm_G' x3 \<open>{u3,x''} \<in> M'\<close> have "{u3,x3} \<notin> M'"            
            by (auto dest: ranking_matching_unique_match)

          with less x3 \<open>u \<noteq> u3\<close> \<open>x \<noteq> x3\<close> show ?thesis
            by auto
        qed
      qed
    qed
  qed
qed

lemma shifts_to_implies_reduced_edge:
  assumes rm_G: "ranking_matching G M \<pi> \<sigma>"
  assumes "ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>"
  assumes "x \<in> set \<sigma>"
  assumes "{u,x} \<in> M"

  assumes x_to_x': "shifts_to G M u x x' \<pi> \<sigma>"
  shows "{u,x'} \<in> M'"
proof (rule ccontr)
  assume "{u,x'} \<notin> M'"

  from \<open>ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>\<close> have rm_G': "ranking_matching (G \<setminus> {x}) M' \<pi> \<sigma>" by (auto dest: ranking_matching_commute)

  from x_to_x' rm_G \<open>x \<in> set \<sigma>\<close> have "{u,x'} \<in> G \<setminus> {x}"
    by (auto intro!: in_remove_verticesI simp: shifts_to_def dest: ranking_matchingD bipartite_disjointD)

  with \<open>{u,x'} \<notin> M'\<close> rm_G' consider (u_matched) "\<exists>x''. {u,x''} \<in> M'" | (u_unmatched) "\<exists>u'. {u',x'} \<in> M'"
    by (metis graph_abs_no_edge_no_vertex insert_commute maximal_matching_def ranking_matchingD)

  then show False
  proof cases
    case u_matched
    then obtain x'' where "{u,x''} \<in> M'" by blast
    with rm_G assms \<open>{u,x'} \<notin> M'\<close> x_to_x' show False
      by (auto dest: ranking_matching_shifts_to_reduced_edges shifts_to_inj)
  next
    case u_unmatched
    then obtain u' where "{u',x'} \<in> M'" by blast

    with rm_G' have "{u',x'} \<in> G"
      by (auto dest: ranking_matchingD remove_vertices_subgraph')

    from \<open>{u',x'} \<in> M'\<close> \<open>{u,x'} \<notin> M'\<close> assms rm_G consider (before_u) "index \<pi> u' < index \<pi> u" | (after_u) "index \<pi> u < index \<pi> u'"
      by (metis index_eq_index_conv less_linear ranking_matching_bipartite_edges')
    then show ?thesis
    proof cases
      case before_u
      have "{u',x'} \<in> M"
      proof (rule ccontr)
        assume \<open>{u',x'} \<notin> M\<close>

        with rm_G \<open>{u',x'} \<in> G\<close> consider (u'_matched) "\<exists>x''. {u',x''} \<in> M" | (u'_unmatched) "\<exists>u''. {u'',x'} \<in> M"
          by (metis graph_abs_no_edge_no_vertex insert_commute maximal_matching_def ranking_matchingD)

        then show False
        proof cases
          case u'_matched
          then obtain x'' where "{u',x''} \<in> M" by blast

          with \<open>{u',x'} \<notin> M\<close> x_to_x' consider (before_x') "index \<sigma> x'' < index \<sigma> x'" | (after_x') "index \<sigma> x' < index \<sigma> x''"
            by (metis index_eq_index_conv nat_neq_iff shifts_to_only_from_input(2))

          then show ?thesis
          proof cases
            case before_x'
            with before_u \<open>{u',x''} \<in> M\<close> \<open>{u',x'} \<in> M'\<close> show ?thesis
            proof (induction "index \<pi> u'" arbitrary: u' x'' x' rule: less_induct)
              case less

              then have "x \<noteq> u'"
                by (metis IntI assms(3) bipartite_disjointD empty_iff index_less_in_set ranking_matchingD rm_G)

              have "u \<noteq> u'"
                using less.prems(1) by blast

              with rm_G \<open>{u,x} \<in> M\<close> \<open>{u',x''} \<in> M\<close> \<open>index \<pi> u' < index \<pi> u\<close> have "x \<noteq> x''"
                by (auto dest: ranking_matching_unique_match')

              with rm_G \<open>{u',x''} \<in> M\<close> \<open>x \<noteq> u'\<close> have "{u',x''} \<in> G \<setminus> {x}"
                by (auto intro: in_remove_verticesI dest: ranking_matchingD)

              with rm_G' \<open>{u',x'} \<in> M'\<close> \<open>index \<sigma> x'' < index \<sigma> x'\<close> obtain u'' where u'': "{u'',x''} \<in> M'" "index \<pi> u'' < index \<pi> u'"
                by (auto elim!: ranking_matching_earlier_match_onlineE)

              with rm_G' have "{u'',x''} \<in> G"
                by (auto dest: ranking_matchingD remove_vertices_subgraph')

              with rm_G \<open>{u',x''} \<in> M\<close> \<open>index \<pi> u'' < index \<pi> u'\<close> obtain x3 where "{u'',x3} \<in> M" "index \<sigma> x3 < index \<sigma> x''"
                by (auto elim: ranking_matching_earlier_match_offlineE)

              with less u''
              show ?case 
                by auto
            qed
          next
            case after_x'
            with rm_G before_u x_to_x' \<open>{u',x''} \<in> M\<close> \<open>{u',x'} \<in> G\<close> show ?thesis
              by (meson order.strict_trans ranking_matching_earlier_match_onlineE shifts_to_def)
          qed
        next
          case u'_unmatched
          then obtain u'' where "{u'',x'} \<in> M" by blast

          with \<open>{u',x'} \<notin> M\<close> before_u consider (before_u') "index \<pi> u'' < index \<pi> u'" | (after_u') "index \<pi> u' < index \<pi> u''"
            by (metis index_eq_index_conv index_less_in_set neqE)

          then show ?thesis
          proof cases
            case before_u'
            with \<open>{u'',x'} \<in> M\<close> x_to_x' before_u show ?thesis
              unfolding shifts_to_def
              by auto
          next
            case after_u'
            with \<open>{u'',x'} \<in> M\<close> \<open>{u',x'} \<in> M'\<close> before_u show ?thesis
            proof (induction "index \<pi> u''" arbitrary: u'' x' u' rule: less_induct)
              case less
              with rm_G' have "{u',x'} \<in> G" by (auto dest: ranking_matchingD remove_vertices_subgraph')

              with rm_G less  obtain x'' where "{u',x''} \<in> M" "index \<sigma> x'' < index \<sigma> x'"
                by (auto elim: ranking_matching_earlier_match_offlineE)

              have "x \<noteq> u'"
                by (metis More_Graph.bipartite_def assms(3) disjoint_insert(1) index_less_in_set insert_absorb less.prems(3) ranking_matchingD rm_G)

              have "u \<noteq> u'"
                using \<open>index \<pi> u' < index \<pi> u\<close> by blast

              with rm_G \<open>{u,x} \<in> M\<close> \<open>index \<pi> u' < index \<pi> u\<close> \<open>{u',x''} \<in> M\<close> have "x \<noteq> x''"
                by (auto dest: ranking_matching_unique_match')

              with rm_G \<open>{u',x''} \<in> M\<close> \<open>x \<noteq> u'\<close> have "{u',x''} \<in> G \<setminus> {x}"
                by (auto intro: in_remove_verticesI dest: ranking_matchingD)

              with rm_G' \<open>{u',x'} \<in> M'\<close> \<open>index \<sigma> x'' < index \<sigma> x'\<close> obtain u3 where "{u3,x''} \<in> M'" "index \<pi> u3 < index \<pi> u'"
                by (auto elim: ranking_matching_earlier_match_onlineE)

              with less \<open>{u',x''} \<in> M\<close>
              show ?case
                by fastforce
            qed
          qed
        qed
      qed

      with x_to_x' before_u show ?thesis unfolding shifts_to_def by blast
    next
      case after_u

      with rm_G' \<open>{u,x'} \<in> G \<setminus> {x}\<close> \<open>{u',x'} \<in> M'\<close> obtain x'' where "{u,x''} \<in> M'" "index \<sigma> x'' < index \<sigma> x'"
        by (auto elim: ranking_matching_earlier_match_offlineE)

      with assms rm_G x_to_x' show ?thesis
        by (metis nat_neq_iff ranking_matching_shifts_to_reduced_edges shifts_to_inj)
    qed
  qed
qed

lemma shifts_to_implies_original_edge:
  assumes rm_G: "ranking_matching G M \<pi> \<sigma>"
  assumes "ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>"
  assumes "x \<in> set \<sigma>"
  assumes "{u,x} \<in> M"
  assumes "{u,x'} \<in> M'"

  assumes u_to_u': "shifts_to (G \<setminus> {x}) M' x' u u' \<sigma> \<pi>"
  shows "{u',x'} \<in> M"
proof (rule ccontr)
  assume "{u',x'} \<notin> M"

  from \<open>ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>\<close> have rm_G': "ranking_matching (G \<setminus> {x}) M' \<pi> \<sigma>" by (auto dest: ranking_matching_commute)

  from u_to_u' have "{u',x'} \<in> G" "{u',x'} \<in> G \<setminus> {x}"
    unfolding shifts_to_def
    by (auto simp: insert_commute dest: remove_vertices_subgraph')

  from u_to_u' have \<open>index \<pi> u < index \<pi> u'\<close> unfolding shifts_to_def by blast

  with \<open>{u',x'} \<notin> M\<close> rm_G consider (u'_matched) "\<exists>x''. {u',x''} \<in> M" | (u'_unmatched) "\<exists>u''. {u'',x'} \<in> M"
    by (metis \<open>{u', x'} \<in> G\<close> graph_abs_no_edge_no_vertex insert_commute maximal_matching_def ranking_matchingD)

  then show False
  proof cases
    case u'_matched
    then obtain x'' where "{u',x''} \<in> M" by blast

    have "x \<noteq> u'"
      by (metis edges_are_Vs insertI1 insert_commute remove_vertices_not_vs shifts_to_def u_to_u')

    from rm_G \<open>{u,x} \<in> M\<close> \<open>{u',x''} \<in> M\<close> \<open>index \<pi> u < index \<pi> u'\<close> have "x \<noteq> x''"
      by (auto dest: ranking_matching_unique_match')

    with rm_G \<open>{u',x''} \<in> M\<close> \<open>x \<noteq> u'\<close> have "{u',x''} \<in> G \<setminus> {x}"
      by (auto intro: in_remove_verticesI dest: ranking_matchingD)

    from \<open>{u',x''} \<in> M\<close> rm_G u_to_u' \<open>{u',x'} \<notin> M\<close> consider (before_x') "index \<sigma> x'' < index \<sigma> x'" | (after_x') "index \<sigma> x' < index \<sigma> x''"
      by (metis index_eq_index_conv neqE ranking_matching_bipartite_edges shifts_to_only_from_input(2))
    then show ?thesis
    proof cases
      case before_x'

      have "{u',x''} \<in> M'"
      proof (rule ccontr)
        assume "{u',x''} \<notin> M'"
        with rm_G' \<open>{u',x''} \<in> G \<setminus> {x}\<close> consider (u'_matched') "\<exists>x3. {u',x3} \<in> M'" | (u'_unmatched') "\<exists>u''. {u'',x''} \<in> M'"
          by (metis graph_abs_no_edge_no_vertex insert_commute maximal_matching_def ranking_matchingD)

        then show False
        proof cases
          case u'_matched'
          then obtain x3 where "{u',x3} \<in> M'" by blast
          then consider (before_x'') "index \<sigma> x3 < index \<sigma> x''" | (after_x'') "index \<sigma> x'' < index \<sigma> x3"
            by (metis \<open>{u', x''} \<in> M\<close> \<open>{u', x''} \<notin> M'\<close> index_eq_index_conv less_linear ranking_matching_bipartite_edges rm_G shifts_to_only_from_input(2) u_to_u')

          then show ?thesis
          proof cases
            case before_x''
            then show ?thesis
              by (metis (no_types, lifting) \<open>{u', x3} \<in> M'\<close> before_x' insert_commute order.strict_trans shifts_to_def u_to_u')
          next
            case after_x''
            with \<open>{u',x3} \<in> M'\<close> \<open>{u',x''} \<in> G \<setminus> {x}\<close> \<open>{u',x''} \<in> M\<close> before_x' show ?thesis
            proof (induction "index \<pi> u'" arbitrary: u' x3 x'' rule: less_induct)
              case less
              with rm_G' obtain u'' where "{u'',x''} \<in> M'" "index \<pi> u'' < index \<pi> u'"
                by (auto elim: ranking_matching_earlier_match_onlineE)

              with rm_G' have "{u'',x''} \<in> G" by (auto dest: ranking_matchingD remove_vertices_subgraph')

              with rm_G \<open>{u',x''} \<in> M\<close> \<open>index \<pi> u'' < index \<pi> u'\<close> obtain x4 where "{u'',x4} \<in> M" "index \<sigma> x4 < index \<sigma> x''"
                by (auto elim: ranking_matching_earlier_match_offlineE)

              have "x \<noteq> u''"
                by (metis \<open>index \<pi> u'' < index \<pi> u'\<close> assms(3) bipartite_disjointD index_less_in_set insert_absorb insert_disjoint(2) ranking_matchingD rm_G)

              from rm_G' \<open>{u,x'} \<in> M'\<close> \<open>{u'',x''} \<in> M'\<close> \<open>index \<sigma> x'' < index \<sigma> x'\<close> have "u \<noteq> u''"
                by (auto dest: ranking_matching_unique_match)

              have "x \<noteq> x4"
                by (metis \<open>u \<noteq> u''\<close> \<open>{u'', x4} \<in> M\<close> assms(4) ranking_matching_def rm_G the_match)

              with rm_G \<open>{u'',x4} \<in> M\<close> \<open>x \<noteq> u''\<close> have "{u'',x4} \<in> G \<setminus> {x}"
                by (auto intro: in_remove_verticesI dest: ranking_matchingD)

              with less \<open>index \<pi> u'' < index \<pi> u'\<close> \<open>{u'',x''} \<in> M'\<close> \<open>{u'',x4} \<in> M\<close> \<open>index \<sigma> x4 < index \<sigma> x''\<close>
              show ?case
                by fastforce
            qed
          qed
        next
          case u'_unmatched'
          then obtain u'' where "{u'',x''} \<in> M'" by blast

          then consider (before_u') "index \<pi> u'' < index \<pi> u'" | (after_u') "index \<pi> u' < index \<pi> u''"
            by (metis \<open>{u', x''} \<notin> M'\<close> index_eq_index_conv nat_neq_iff shifts_to_only_from_input(2) u_to_u')

          then show ?thesis
          proof cases
            case before_u'
            with \<open>{u'',x''} \<in> M'\<close> \<open>{u',x''} \<in> M\<close> before_x' show ?thesis
            proof (induction "index \<sigma> x''" arbitrary: x'' u' u'' rule: less_induct)
              case less
              with rm_G' have "{u'',x''} \<in> G" by (auto dest: ranking_matchingD remove_vertices_subgraph')

              with less rm_G obtain x3 where x3: "{u'',x3} \<in> M" "index \<sigma> x3 < index \<sigma> x''"
                by (auto elim: ranking_matching_earlier_match_offlineE)

              have "x \<noteq> u''"
                by (metis IntI assms(4) bipartite_disjointD empty_iff index_less_in_set less.prems(4) ranking_matchingD ranking_matching_bipartite_edges' ranking_matching_commute rm_G shifts_to_only_from_input(1) u_to_u')

              from rm_G' \<open>{u, x'} \<in> M'\<close> \<open>{u'', x''} \<in> M'\<close> \<open>index \<sigma> x'' < index \<sigma> x'\<close> have "u \<noteq> u''"
                by (auto dest: ranking_matching_unique_match)

              then have "x \<noteq> x3"
                by (metis (no_types, lifting) assms(4) ranking_matching_def rm_G the_match x3(1))

              with rm_G \<open>{u'',x3} \<in> M\<close> \<open>x \<noteq> u''\<close> have "{u'',x3} \<in> G \<setminus> {x}"
                by (auto intro: in_remove_verticesI dest: ranking_matchingD)

              with rm_G' \<open>{u'',x''} \<in> M'\<close> \<open>index \<sigma> x3 < index \<sigma> x''\<close> obtain u3 where "{u3,x3} \<in> M'" "index \<pi> u3 < index \<pi> u''"
                by (auto elim: ranking_matching_earlier_match_onlineE)

              with less x3
              show ?case
                by auto
            qed
          next
            case after_u'
            then show ?thesis
              by (smt (verit, ccfv_threshold) \<open>{u'', x''} \<in> M'\<close> \<open>{u', x''} \<in> G \<setminus> {x}\<close> assms(5) before_x' insert_commute not_less_iff_gr_or_eq order.strict_trans ranking_matching_bipartite_edges ranking_matching_def rm_G' shifts_to_matched_vertex_later_match shifts_to_only_from_input(1) u_to_u')
          qed
        qed
      qed

      with before_x' u_to_u' show ?thesis
        unfolding shifts_to_def
        by (auto simp: insert_commute)
    next
      case after_x'
      with rm_G \<open>{u',x''} \<in> M\<close> \<open>{u',x'} \<in> G\<close> obtain u'' where "{u'',x'} \<in> M" "index \<pi> u'' < index \<pi> u'"
        by (auto elim: ranking_matching_earlier_match_onlineE)

      then consider (before_u) "index \<pi> u'' < index \<pi> u" | (after_u) "index \<pi> u < index \<pi> u''"
        by (metis (no_types, lifting) \<open>{u', x'} \<in> G \<setminus> {x}\<close> assms(4) edges_are_Vs(2) index_eq_index_conv linorder_neqE_nat ranking_matching_def remove_vertices_not_vs rm_G shifts_to_only_from_input(1) singletonI the_match' u_to_u')

      then show ?thesis
      proof cases
        case before_u
        then show ?thesis
          by (metis \<open>index \<pi> u < index \<pi> u'\<close> \<open>{u'', x'} \<in> M\<close> assms(2) assms(3) assms(4) assms(5) index_less_in_set not_less_iff_gr_or_eq ranking_matching_def ranking_matching_shifts_to_reduced_edges rm_G shifts_to_matched_vertex_later_match)
      next
        case after_u
        then show ?thesis
          by (smt (verit, ccfv_threshold) \<open>index \<pi> u'' < index \<pi> u'\<close> \<open>{u'', x'} \<in> M\<close> assms(1) assms(2) assms(3) assms(4) assms(5) ranking_matching_shifts_to_original_edges shifts_to_def u_to_u')
      qed
    qed
  next
    case u'_unmatched
    then obtain u'' where "{u'',x'} \<in> M" by blast
    then show ?thesis
      by (smt (verit, best) \<open>index \<pi> u < index \<pi> u'\<close> \<open>{u', x'} \<notin> M\<close> assms(2) assms(3) assms(4) assms(5) index_less_in_set ranking_matching_def ranking_matching_shifts_to_original_edges ranking_matching_shifts_to_reduced_edges rm_G shifts_to_inj shifts_to_matched_vertex_later_match u_to_u')
  qed
qed


lemma ranking_matching_zig_zag_eq:
  assumes "{u,x} \<in> M"
  assumes "x \<in> set \<sigma>"
  assumes "ranking_matching G M \<pi> \<sigma>"
  assumes "ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>"
  shows "zig (G \<setminus> {x}) M' u \<sigma> \<pi> = zag G M u \<pi> \<sigma>"
  using assms
proof (induction "length \<pi> - index \<pi> u" arbitrary: u x G M M' rule: less_induct)
  case less
  let ?lhs = "zig (G \<setminus> {x}) M' u \<sigma> \<pi>"
  and ?rhs = "zag G M u \<pi> \<sigma>"

  have matching_M: "matching M" and matching_M': "matching M'" using less
    by (auto dest: ranking_matchingD maximal_matchingD)

  with \<open>{u,x} \<in> M\<close> have x_unique_match: "(THE x. {u,x} \<in> M) = x"
    by (auto simp: insert_commute intro: the_match)

  from less show ?case
  proof (cases "\<exists>x'. {x',u} \<in> M'")
    case True
    then obtain x' where x'u_in_M': "{x',u} \<in> M'" by blast

    with matching_M' have unique_u_M'_match: "(THE x'. {x',u} \<in> M') = x'"
      by (auto intro: the_match)
 

    with \<open>{x',u} \<in> M'\<close> matching_M' have lhs_Cons: "?lhs = u # zag (G \<setminus> {x}) M' x' \<sigma> \<pi>"
      by (auto simp: zig.simps)
      

    from \<open>{x',u} \<in> M'\<close> matching_M' have unique_x'_M'_match: "(THE u. {x',u} \<in> M') = u"
      by (auto simp: insert_commute intro: the_match)
   

    from \<open>ranking_matching G M \<pi> \<sigma>\<close> \<open>ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>\<close> \<open>x \<in> set \<sigma>\<close> \<open>{u,x} \<in> M\<close>
      \<open>{x',u} \<in> M'\<close>
    have x_to_x': "shifts_to G M u x x' \<pi> \<sigma>"
      by (auto intro!: ranking_matching_shifts_to_reduced_edges simp: insert_commute)

    then have the_x_to_x': "(THE x'. shifts_to G M u x x' \<pi> \<sigma>) = x'"
      by (simp add: the_shifts_to)

    from x_to_x' have "x \<in> set \<sigma>" "x' \<in> set \<sigma>"
      by (meson shifts_to_only_from_input)+

    from x_to_x' the_x_to_x' x_unique_match \<open>{u,x} \<in> M\<close> matching_M have rhs_Cons: "?rhs = u # zig G M x' \<pi> \<sigma>"
      by (auto simp: zag.simps)


    show ?thesis
    proof (cases "\<exists>u'. {u',x'} \<in> M")
      case True
      then obtain u' where "{u',x'} \<in> M" by blast

      with matching_M have "(THE u'. {u',x'} \<in> M) = u'"
        by (auto intro: the_match)

      with \<open>{u',x'} \<in> M\<close> matching_M have rhs: "zig G M x' \<pi> \<sigma> = x' # zag G M u' \<pi> \<sigma>"
        by (auto simp: zig.simps)

      from \<open>{u,x} \<in> M\<close> \<open>{u',x'} \<in> M\<close> \<open>matching M\<close> x_to_x' have "index \<pi> u < index \<pi> u'"
        by (auto intro!: shifts_to_matched_vertex_later_match simp: shifts_to_def)

      with \<open>ranking_matching G M \<pi> \<sigma>\<close> \<open>ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>\<close> \<open>x \<in> set \<sigma>\<close> \<open>{u,x} \<in> M\<close>
        \<open>{x',u} \<in> M'\<close> \<open>{u',x'} \<in> M\<close>
      have u_to_u': "shifts_to (G \<setminus> {x}) M' x' u u' \<sigma> \<pi>"
        by (auto intro!: ranking_matching_shifts_to_original_edges simp: insert_commute)

      then have the_u_to_u': "(THE u'. shifts_to (G \<setminus> {x}) M' x' u u' \<sigma> \<pi>) = u'"
        by (simp add: the_shifts_to)

      with u_to_u' \<open>{x',u} \<in> M'\<close> unique_x'_M'_match matching_M' have lhs: "zag (G \<setminus> {x}) M' x' \<sigma> \<pi> = x' # zig (G \<setminus> {x}) M' u' \<sigma> \<pi>"
        by (auto simp: zag.simps)

      from u_to_u' have less_prem: "length \<pi> - index \<pi> u' < length \<pi> - index \<pi> u"
        unfolding shifts_to_def
        by (metis diff_less_mono2 dual_order.asym index_conv_size_if_notin index_less_size_conv)


      from \<open>ranking_matching G M \<pi> \<sigma>\<close> \<open>{u,x} \<in> M\<close> have ranking_matching_reduced: "ranking_matching (G \<setminus> {u,x}) (M \<setminus> {u,x}) \<pi> \<sigma>"
        by (simp add: remove_edge_ranking_matching)

      from \<open>{u',x'} \<in> M\<close> \<open>matching M\<close> have "{u', x'} \<in> M \<setminus> {u, x}"
        by (metis \<open>index \<pi> u < index \<pi> u'\<close> doubleton_eq_iff dual_order.strict_implies_not_eq graph_abs_edgeD insertE insert_Diff less.prems(1) less.prems(4) ranking_matchingD remove_edge_matching x'u_in_M')
        

      have "G \<setminus> {u,x} \<setminus> {x'} = G \<setminus> {x} \<setminus> {u,x'}"
        by (simp add: remove_remove_union insert_commute)

      with \<open>ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>\<close> \<open>{x',u} \<in> M'\<close> have ranking_matching_reduced': "ranking_matching (G \<setminus> {u,x} \<setminus> {x'}) (M' \<setminus> {u,x'}) \<sigma> \<pi>"
        by (auto dest!: remove_edge_ranking_matching simp: insert_commute)


      have "x \<notin> Vs M'"
        by (meson Vs_subset insertI1 less.prems(4) ranking_matchingD remove_vertices_not_vs subsetD)
      then have "M' \<setminus> {x} = M'"
        by (subst remove_vertices_only_vs)
           (simp add: remove_vertices_empty)

      have "x' \<in> Vs M'"
        by (meson edges_are_Vs(1) x'u_in_M')

      with \<open>x \<notin> Vs M'\<close> have "M' \<setminus> {x,x'} = M' \<setminus> {x'}"
        by (subst remove_vertices_only_vs) simp

      then have "zig (G \<setminus> {u, x} \<setminus> {x'}) (M' \<setminus> {u, x'}) u' \<sigma> \<pi> = zig (G \<setminus> {x} \<setminus> {x'} \<setminus> {u}) (M' \<setminus> {x} \<setminus> {x'} \<setminus> {u}) u' \<sigma> \<pi>"
        by (simp add: insert_commute remove_remove_union)

      also have "\<dots> = zig (G \<setminus> {x} \<setminus> {x'}) (M' \<setminus> {x} \<setminus> {x'}) u' \<sigma> \<pi>"
        apply (rule remove_offline_vertices_zig_zig_eq)
            apply (meson empty_subsetI insert_subset shifts_to_only_from_input(1) u_to_u')
           apply (simp add: matching_M' matching_remove_vertices)
        using bipartite_remove_vertices less.prems(4) ranking_matchingD apply blast
         apply (metis shifts_to_def u_to_u')
        using \<open>index \<pi> u < index \<pi> u'\<close> by blast

      also have "\<dots> = zig (G \<setminus> {x}) (M' \<setminus> {x}) u' \<sigma> \<pi>"
        apply (intro remove_online_vertices_zig_zig_eq)
        using \<open>x' \<in> set \<sigma>\<close> less.prems(2) apply blast
        using bipartite_remove_vertices less.prems(4) ranking_matchingD apply blast
        using matching_M' matching_remove_vertices apply blast
         apply (meson shifts_to_only_from_input(2) u_to_u')
        by (metis \<open>index \<pi> u < index \<pi> u'\<close> empty_iff insert_iff matching_M' matching_remove_vertices remove_vertices_subgraph' the_match' unique_x'_M'_match)

      also have "\<dots> = zig (G \<setminus> {x}) M' u' \<sigma> \<pi>"
        by (simp add: \<open>M' \<setminus> {x} = M'\<close>)

      finally have zig_zig_eq: "zig (G \<setminus> {u, x} \<setminus> {x'}) (M' \<setminus> {u, x'}) u' \<sigma> \<pi> = zig (G \<setminus> {x}) M' u' \<sigma> \<pi>" .

      have "index \<sigma> x < index \<sigma> x'"
        by (meson shifts_to_def x_to_x')

      have "zag (G \<setminus> {u, x}) (M \<setminus> {u, x}) u' \<pi> \<sigma> = zag (G \<setminus> {x} \<setminus> {u}) (M \<setminus> {x} \<setminus> {u}) u' \<pi> \<sigma>"
        by (simp add: remove_remove_union)

      also have "\<dots> = zag (G \<setminus> {x}) (M \<setminus> {x}) u' \<pi> \<sigma>"
        apply (rule remove_online_vertices_zag_zag_eq)
            apply (meson empty_subsetI insert_subset shifts_to_only_from_input(1) u_to_u')
        using bipartite_remove_vertices less.prems(3) ranking_matchingD apply blast
          apply (simp add: matching_M matching_remove_vertices)
         apply (metis shifts_to_def u_to_u')
        by (metis edges_are_Vs(1) less.prems(1) matching_M remove_vertex_matching_vs remove_vertex_matching_vs' remove_vertices_not_vs)
      
      also have  "\<dots> = zag G M u' \<pi> \<sigma>"
        apply (intro remove_offline_vertices_zag_zag_eq)
            apply (simp add: less.prems(2))
        using matching_M apply blast
        using less.prems(3) ranking_matchingD apply blast
         apply (meson shifts_to_only_from_input(2) u_to_u')
        using \<open>index \<sigma> x < index \<sigma> x'\<close> \<open>{u', x'} \<in> M\<close> matching_M the_match' by fastforce

      finally have zag_zag_eq: "zag (G \<setminus> {u, x}) (M \<setminus> {u, x}) u' \<pi> \<sigma> = zag G M u' \<pi> \<sigma>" .
      
      with zig_zig_eq zag_zag_eq \<open>M' \<setminus> {x} = M'\<close>
        less.hyps[OF less_prem \<open>{u',x'} \<in> M \<setminus> {u,x}\<close> \<open>x' \<in> set \<sigma>\<close> ranking_matching_reduced ranking_matching_reduced']
      show ?thesis
        unfolding lhs_Cons rhs_Cons lhs rhs
        by auto
        

    next
      case False

      with matching_M have rhs: "zig G M x' \<pi> \<sigma> = [x']"
        by (simp add: zig.simps)


      with False \<open>ranking_matching G M \<pi> \<sigma>\<close> \<open>ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>\<close> \<open>{u,x} \<in> M\<close> \<open>{x',u} \<in> M'\<close> \<open>x \<in> set \<sigma>\<close>
      have "\<nexists>u'. shifts_to (G \<setminus> {x}) M' x' u u' \<sigma> \<pi>"
        by (meson shifts_to_implies_original_edge shifts_to_implies_reduced_edge x_to_x')

      with \<open>{x',u} \<in> M'\<close> unique_x'_M'_match matching_M' have lhs: "zag (G \<setminus> {x}) M' x' \<sigma> \<pi> = [x']"
        by (auto simp: zag.simps)

      with lhs_Cons rhs_Cons rhs show ?thesis by simp
    qed
  next
    case False
    with matching_M' have lhs: "zig (G \<setminus> {x}) M' u \<sigma> \<pi> = [u]"
      by (simp add: zig.simps)

    with \<open>ranking_matching G M \<pi> \<sigma>\<close> \<open>ranking_matching (G \<setminus> {x}) M' \<sigma> \<pi>\<close> \<open>x \<in> set \<sigma>\<close> \<open>{u,x} \<in> M\<close> False
    have "\<nexists>x'. shifts_to G M u x x' \<pi> \<sigma>"
      thm shifts_to_implies_reduced_edge
      by (metis (full_types) insert_commute shifts_to_implies_reduced_edge)

    with x_unique_match \<open>{u,x} \<in> M\<close> matching_M have rhs: "zag G M u \<pi> \<sigma> = [u]"
      by (auto simp: zag.simps)

    show ?thesis
      unfolding lhs rhs by (rule refl)
  qed
qed

end