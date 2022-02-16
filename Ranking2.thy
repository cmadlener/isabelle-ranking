theory Ranking2
  imports
    More_Graph
    More_List
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

lemma ranking'_append: "ranking' G (us@us') \<sigma> M = ranking' G us' \<sigma> (ranking' G us \<sigma> M)"
  by (simp add: ranking_foldl)

lemma ranking_append: "ranking G (us@us') \<sigma> = ranking' G us' \<sigma> (ranking G us \<sigma>)"
  by (simp add: ranking'_append)

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
| no_matching_zig: "zig _ M v _ _ = [v]" if "\<not>matching M"

| proper_zag: "zag G M u \<pi> \<sigma> =  u # (if \<exists>v. {u,v} \<in> M
                      then 
                      (let v = THE v. {u,v} \<in> M in (
                        if \<exists>v'. shifts_to G M u v v' \<pi> \<sigma>
                        then zig G M (THE v'. shifts_to G M u v v' \<pi> \<sigma>) \<pi> \<sigma>
                        else [])
                      )
                      else []
                    )" if "matching M"
| no_matching_zag: "zag _ M v _ _ = [v]" if "\<not>matching M"
  by auto (smt (z3) prod_cases5 sum.collapse)

definition zig_zag_relation where
  "zig_zag_relation \<equiv>
    {(Inr (G, M, u, \<pi>, \<sigma>), Inl (G, M, v, \<pi>, \<sigma>)) | (G :: 'a graph) M u v \<pi> \<sigma>. matching M \<and> {u,v} \<in> M \<and> ((\<exists>v'. shifts_to G M u v v' \<pi> \<sigma>) \<longrightarrow> index \<sigma> v < index \<sigma> (THE v'. shifts_to G M u v v' \<pi> \<sigma>))} \<union>
    {(Inl (G, M, v', \<pi>, \<sigma>), Inr (G, M, u, \<pi>, \<sigma>)) | (G :: 'a graph) M u v' \<pi> \<sigma>. matching M \<and> (\<exists>v. {u,v} \<in> M \<and> shifts_to G M u (THE v. {u,v} \<in> M) v' \<pi> \<sigma>) \<and> index \<sigma> (THE v. {u,v} \<in> M) < index \<sigma> v'}"


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

lemma zig_zag_induct:
  assumes "\<And>G M v \<pi> \<sigma>. matching M \<Longrightarrow> (\<And>u. {u,v} \<in> M \<Longrightarrow> (THE u. {u,v} \<in> M) = u \<Longrightarrow> Q G M u \<pi> \<sigma> \<Longrightarrow> P G M v \<pi> \<sigma>)"
  assumes "\<And>G M v \<pi> \<sigma>. matching M \<Longrightarrow> \<nexists>u. {u,v} \<in> M \<Longrightarrow> P G M v \<pi> \<sigma>"
  assumes "\<And>G M v \<pi> \<sigma>. \<not>matching M \<Longrightarrow> P G M v \<pi> \<sigma>"
  assumes "\<And>G M u \<pi> \<sigma>. matching M \<Longrightarrow> (\<And>v v'. {u, v} \<in> M \<Longrightarrow> shifts_to G M u v v' \<pi> \<sigma> \<Longrightarrow> P G M v' \<pi> \<sigma>) \<Longrightarrow> Q G M u \<pi> \<sigma>"
  assumes "\<And>G M u \<pi> \<sigma>. \<not>matching M \<Longrightarrow> Q G M u \<pi> \<sigma>"
  shows "P G M v \<pi> \<sigma>" and "Q G M u \<pi> \<sigma>"
proof (induction G M v \<pi> \<sigma> and G M u \<pi> \<sigma> rule: zig_zag.induct)
  case (1 M G v \<pi> \<sigma>)
  then show ?case
  proof (cases "\<exists>u. {u,v} \<in> M")
    case True
    then obtain u where "{u,v} \<in> M" by blast
    with \<open>matching M\<close> have "(THE u. {u,v} \<in> M) = u"
      by (simp add: the_match)
    with True assms 1 \<open>{u,v} \<in> M\<close> show ?thesis
      by blast
  next
    case False
    with assms 1 show ?thesis
      by blast
  qed
next
  case (3 M G u \<pi> \<sigma>)
  then show ?case
  proof (cases "\<exists>v. {u,v} \<in> M")
    case True
    then obtain v where "{u,v} \<in> M" by blast
    with \<open>matching M\<close> have the_v: "(THE v. {u,v} \<in> M) = v"
      by (simp add: the_match')

    then show ?thesis
    proof (cases "\<exists>v'. shifts_to G M u v v' \<pi> \<sigma>")
      case True
      then obtain v' where shifts_to: "shifts_to G M u v v' \<pi> \<sigma>" by blast
      then have "(THE v'. shifts_to G M u v v' \<pi> \<sigma>) = v'"
        by (simp add: the_shifts_to)

      with "3.IH"[OF \<open>\<exists>v. {u,v} \<in> M\<close> the_v[symmetric] True, simplified this]
      assms(4)[OF \<open>matching M\<close> ] show ?thesis
        by (metis "3.hyps" \<open>{u, v} \<in> M\<close> the_match' the_shifts_to)
    next
      case False
      with assms \<open>{u,v} \<in> M\<close> show ?thesis
        by (metis the_match')
    qed
  next
    case False
    with assms show ?thesis
      by metis
  qed
qed (use assms in auto)

lemma zag_casesE:
  obtains "\<exists>v. {u,v} \<in> M \<and> (\<exists>v'. shifts_to G M u v v' \<pi> \<sigma>)" | "\<exists>v. {u,v} \<in> M \<and> (\<nexists>v'. shifts_to G M u v v' \<pi> \<sigma>)" | "\<nexists>v. {u,v} \<in> M"
  by blast

declare zig.simps[simp del] zag.simps[simp del]


fun_cases zig_ConsE: "zig G M v \<pi> \<sigma> = v' # uvs"
fun_cases zig_SingleE: "zig G M v \<pi> \<sigma> = [v']"
fun_cases zig_NilE: "zig G M v \<pi> \<sigma> = []"
thm zig_ConsE zig_SingleE zig_NilE

lemmas zig_symE = zig_ConsE[OF sym] zig_SingleE[OF sym] zig_NilE[OF sym]

fun_cases zag_ConsE: "zag G M u \<pi> \<sigma> = u' # uvs"
fun_cases zag_SingleE: "zag G M u \<pi> \<sigma> = [u']"
fun_cases zag_NilE: "zag G M u \<pi> \<sigma> = []"
thm zag_ConsE zag_SingleE zag_NilE

lemmas zag_symE = zag_ConsE[OF sym] zag_SingleE[OF sym] zag_NilE[OF sym]

lemma hd_zig: "hd (zig G M x \<pi> \<sigma>) = x"
  by (cases "matching M")
     (auto simp: zig.simps)

lemma zig_hdE:
  obtains uvs where "zig G M v \<pi> \<sigma> = v # uvs"
  by (cases "matching M")
     (auto simp: zig.simps)

lemma zag_hdE:
  obtains vus where "zag G M u \<pi> \<sigma> = u # vus"
  by (cases "matching M")
     (auto simp: zag.simps)

lemma zig_Cons_zagE:
  assumes "zig G M v \<pi> \<sigma> = v' # zag G M u \<pi> \<sigma>"
  obtains "v = v'" "{u,v} \<in> M" "matching M"
  using assms
  by (auto elim: zig_ConsE zag_NilE zag_hdE split: if_splits simp: the_match zag.simps)
  
lemma zag_Cons_zigE:
  assumes "zag G M u \<pi> \<sigma> = u' # zig G M v' \<pi> \<sigma>"
  obtains v where "u = u'" "{u,v} \<in> M" "shifts_to G M u v v' \<pi> \<sigma>" "matching M"
  using assms
  by (auto elim!: zag_ConsE zig_NilE zig_hdE split: if_splits 
      simp: the_match' zig.simps the_shifts_to)

lemma zag_no_shifts_to:
  "{u,v} \<in> M \<Longrightarrow> \<nexists>v'. shifts_to G M u v v' \<pi> \<sigma> \<Longrightarrow> zag G M u \<pi> \<sigma> = [u]"
  by (cases "matching M")
     (auto simp: zag.simps the_match')

lemma zig_then_zag:
  assumes "zig G M v \<pi> \<sigma> = v' # u # vus"
  shows "zag G M u \<pi> \<sigma> = u # vus"
  using assms
  by (auto elim!: zig_ConsE zag_symE split: if_splits simp: the_match)

lemmas zig_then_zagE = zig_then_zag[elim_format]

lemma zag_then_zig:
  assumes "zag G M u \<pi> \<sigma> = u' # v # uvs"
  shows "zig G M v \<pi> \<sigma> = v # uvs"
  using assms
  by (auto elim!: zag_ConsE zig_symE split: if_splits simp: the_match' the_shifts_to)

lemmas zag_then_zigE = zag_then_zig[elim_format]

lemma zig_matching_edge: "zig G M v \<pi> \<sigma> = v' # u # uvs \<Longrightarrow> {u,v} \<in> M"
  by (auto elim!: zig_ConsE split: if_splits simp: the_match zag.simps)

lemma zag_shift_edge:
  assumes "{u,v} \<in> M"
  assumes "zag G M u \<pi> \<sigma> = u # v' # uvs"
  shows "shifts_to G M u v v' \<pi> \<sigma>"
  using assms
  by (auto elim!: zag_ConsE zig_symE split: if_splits simp: the_match' the_shifts_to)

lemma zig_increasing_ranks:
  assumes "zig G M v \<pi> \<sigma> = v # u # zig G M v' \<pi> \<sigma>"
  shows "index \<sigma> v < index \<sigma> v'"
proof -
  have "{u,v} \<in> M" using assms zig_matching_edge by fast
  then have "(THE u. {u,v} \<in> M) = u" using assms the_match zig_ConsE by fast
  with \<open>{u,v} \<in> M\<close> assms have "zig G M v \<pi> \<sigma> = v # zag G M u \<pi> \<sigma>"
    by (auto elim!: zig_ConsE intro: the_match)

  with assms \<open>{u,v} \<in> M\<close> have "shifts_to G M u v v' \<pi> \<sigma>"
    by (metis zag_shift_edge zig_hdE zig_then_zag)

  then show ?thesis unfolding shifts_to_def by blast
qed

lemma zag_increasing_arrival:
  assumes "zag G M u \<pi> \<sigma> = u # v' # zag G M u' \<pi> \<sigma>"
  shows "index \<pi> u < index \<pi> u'"
proof -
  have "matching M" using assms by (auto elim: zag_ConsE)

  obtain v where "{u,v} \<in> M" using assms
    by (auto elim: zag_ConsE split: if_splits)

  with \<open>{u,v} \<in> M\<close> \<open>matching M\<close> have zig_zag: "zig G M v \<pi> \<sigma> = v # zag G M u \<pi> \<sigma>"
    by (auto simp: zig.simps the_match)

  with assms \<open>{u,v} \<in> M\<close> have shifts_to: "shifts_to G M u v v' \<pi> \<sigma>"
    by (auto dest: zag_shift_edge)

  with \<open>{u,v} \<in> M\<close> \<open>matching M\<close> have "zag G M u \<pi> \<sigma> = u # zig G M v' \<pi> \<sigma>"
    by (fastforce simp: zag.simps the_shifts_to the_match')

  with zig_zag assms have "{u',v'} \<in> M"
    by (meson zag_then_zig zig_Cons_zagE)
    
  with shifts_to show ?thesis
    unfolding shifts_to_def
    by (metis \<open>matching M\<close> \<open>{u, v} \<in> M\<close> index_eq_index_conv linorder_neqE the_match')
qed

lemma
  assumes "bipartite M (set \<pi>) (set \<sigma>)"
  shows
    alt_list_zig: "v \<in> set \<sigma> \<Longrightarrow> alt_list (\<lambda>x. x \<in> set \<sigma>) (\<lambda>x. x \<in> set \<pi>) (zig G M v \<pi> \<sigma>)" and
    alt_list_zag: "u \<in> set \<pi> \<Longrightarrow> alt_list (\<lambda>x. x \<in> set \<pi>) (\<lambda>x. x \<in> set \<sigma>) (zag G M u \<pi> \<sigma>)"
  using assms
proof (induction G M v \<pi> \<sigma> and G M u \<pi> \<sigma> rule: zig_zag_induct)
  case (1 G M v \<pi> \<sigma> u)
  then have "u \<in> set \<pi>"
    by (auto dest: bipartite_edgeD)

  with 1 show ?case
    by (auto simp: zig.simps intro: alt_list.intros)
next
  case (4 G M u \<pi> \<sigma>)
  from zag_casesE[of u M G \<pi> \<sigma>] show ?case
  proof cases
    case 1
    then obtain v v' where vv': "{u,v} \<in> M" "shifts_to G M u v v' \<pi> \<sigma>" by blast
    then have "v' \<in> set \<sigma>"
      by (simp add: shifts_to_only_from_input)

    from vv' \<open>matching M\<close> have "(THE v. {u,v} \<in> M) = v" "(THE v'. shifts_to G M u v v' \<pi> \<sigma>) = v'"
      by (auto dest: the_match' the_shifts_to)

    with 1 4 vv' \<open>v' \<in> set \<sigma>\<close> show ?thesis
      by (auto simp: zag.simps intro: alt_list.intros)
  next
    case 2
    then obtain v where "{u,v} \<in> M" by blast

    with 2 4 show ?thesis
      by (auto simp: zag_no_shifts_to intro!: alt_list.intros)      
  next
    case 3
    with \<open>matching M\<close> \<open>u \<in> set \<pi>\<close> show ?thesis
      by (auto simp: zag.simps intro: alt_list.intros)
  qed
qed (auto simp: zig.simps zag.simps alt_list_step alt_list_empty)


lemma rev_alt_path_zig_edges: "rev_alt_path M (zig G M v \<pi> \<sigma>)"
proof (induction "zig G M v \<pi> \<sigma>" arbitrary: v rule: induct_list012)
  case (2 x)
  from this[symmetric] show ?case
    by (simp add: alt_list_empty)
next
  case (3 v' u vus)
  then have zig_v: "zig G M v \<pi> \<sigma> = v' # u # vus"
    by simp

  then have "{u,v} \<in> M" "v' = v" "matching M"
    by (auto dest: zig_matching_edge elim: zig_ConsE)

  show ?case
  proof (cases vus)
    case Nil
    with zig_v \<open>v' = v\<close> \<open>{u,v} \<in> M\<close> show ?thesis
      by (auto simp: alt_list_step alt_list_empty dest: edge_commute)
  next
    case (Cons v'' uvs)
    with zig_v \<open>v' = v\<close> have "v'' \<noteq> v"
      by (metis "3.hyps"(1) \<open>{u, v} \<in> M\<close> alt_list_step edges_of_path.simps(3) zag_then_zig zig_then_zag)

    with zig_v Cons have "vus = zig G M v'' \<pi> \<sigma>"
      by (auto elim!: zig_then_zagE zag_then_zigE)

    with 3 Cons \<open>v'' \<noteq> v\<close> \<open>v' = v\<close> \<open>{u,v} \<in> M\<close> \<open>matching M\<close> show ?thesis
      by (metis (mono_tags, lifting) alt_list.intros(2) edge_commute edges_of_path.simps(3) the_match)
  qed
qed (simp add: alt_list_empty)

lemma zig_not_augmenting:
  "augmenting_path M (zig G M x \<pi> \<sigma>) \<Longrightarrow> False"
proof (cases "2 \<le> length (zig G M x \<pi> \<sigma>)")
  case True
  assume aug: "augmenting_path M (zig G M x \<pi> \<sigma>)"

  from True obtain v u vus where "zig G M x \<pi> \<sigma> = v # u # vus"
    using length_at_least_two_Cons_Cons by blast

  with aug hd_zig show ?thesis
    unfolding augmenting_path_def
    by (metis edges_are_Vs(2) zig_matching_edge)
next
  case False
  assume "augmenting_path M (zig G M x \<pi> \<sigma>)"
  with False show ?thesis
    unfolding augmenting_path_def by blast
qed

lemma zig_start_wrong_side:
  assumes "u \<notin> set \<sigma>"
  assumes "bipartite M (set \<pi>) (set \<sigma>)"
  obtains v where "zig G M u \<pi> \<sigma> = [u,v]" "{u,v} \<in> M" "v \<in> set \<sigma>" | "zig G M u \<pi> \<sigma> = [u]"
proof (cases "matching M")
  case True
  assume assm: "zig G M u \<pi> \<sigma> = [u] \<Longrightarrow> thesis"
    "(\<And>v. zig G M u \<pi> \<sigma> = [u, v] \<Longrightarrow> {u, v} \<in> M \<Longrightarrow> v \<in> set \<sigma> \<Longrightarrow> thesis)"
  
  show ?thesis
  proof (cases "\<exists>v. {u,v} \<in> M")
    case True
    then obtain v where "{u,v} \<in> M" by blast

    with assms have "v \<in> set \<sigma>"
      by (auto elim: bipartite_edgeE)

    from \<open>u \<notin> set \<sigma>\<close> have "\<nexists>u'. shifts_to G M v u u' \<pi> \<sigma>"
      by (auto dest: shifts_to_only_from_input)

    with \<open>matching M\<close> \<open>{u,v} \<in> M\<close> have "zag G M v \<pi> \<sigma> = [v]"
      by (auto simp: zag.simps dest: the_match'')

    with \<open>matching M\<close> \<open>{u,v} \<in> M\<close> have "zig G M u \<pi> \<sigma> = [u,v]"
      by (auto simp: zig.simps dest: edge_commute the_match''')

    with assm \<open>{u,v} \<in> M\<close> \<open>v \<in> set \<sigma>\<close> show ?thesis
      by blast
  next
    case False
    from False \<open>matching M\<close> have "zig G M u \<pi> \<sigma> = [u]"
      by (auto simp: zig.simps dest: edge_commute)

    with assm show ?thesis
      by blast
  qed
next
  case False
  assume assm: "zig G M u \<pi> \<sigma> = [u] \<Longrightarrow> thesis"

  from \<open>\<not>matching M\<close> have "zig G M u \<pi> \<sigma> = [u]"
    by (simp add: zig.simps)

  with assm show ?thesis
    by blast
qed

lemma sorted_wrt_rank_zig:
  assumes "bipartite M (set \<pi>) (set \<sigma>)"
  shows "sorted_wrt (\<lambda>a b. index \<sigma> a < index \<sigma> b) [x <- zig G M v \<pi> \<sigma>. x \<in> set \<sigma>]"
  using assms
proof (cases "v \<in> set \<sigma>")
  case True
  with assms show ?thesis
  proof (induction "zig G M v \<pi> \<sigma>" arbitrary: v rule: induct_list012)
    case (2 x)
    from this(1)[symmetric] show ?case
      by simp
  next
    case (3 v u vus v')
    then have "{u,v} \<in> M" "v' = v"
      by (metis zig_ConsE zig_matching_edge)+
  
    with 3 have "u \<notin> set \<sigma>"
      by (auto dest: bipartite_edgeD)
  
    show ?case
    proof (cases vus)
      case Nil
      with 3(3)[symmetric] \<open>u \<notin> set \<sigma>\<close> show ?thesis
        by simp
    next
      case (Cons v'' uvs)
      with 3 have vus_zig: "vus = zig G M v'' \<pi> \<sigma>"
        by (metis zag_then_zig zig_then_zag)
  
      with 3 have "v'' \<in> set \<sigma>"
        by (metis shifts_to_only_from_input(2) zag_Cons_zigE zig_then_zag)
  
      from 3(3)[symmetric] vus_zig \<open>v' = v\<close> \<open>u \<notin> set \<sigma>\<close> \<open>v' \<in> set \<sigma>\<close> have "[x <- zig G M v' \<pi> \<sigma>. x \<in> set \<sigma>] = v # [x <- zig G M v'' \<pi> \<sigma>. x \<in> set \<sigma>]"
        by auto
  
      with 3 vus_zig \<open>v' = v\<close> \<open>v'' \<in> set \<sigma>\<close> show ?thesis
        apply (auto simp flip: successively_conv_sorted_wrt[OF transp_index_less])
        by (metis (mono_tags, lifting) filter.simps(2) list.sel(1) local.Cons successively_Cons zig_increasing_ranks)
    qed
  qed simp
next
  case False
  with assms show ?thesis
    by (auto elim!: zig_start_wrong_side[where G = G] dest: bipartite_edgeD)
qed

lemma zag_start_wrong_side:
  assumes "v \<notin> set \<pi>"
  assumes "bipartite M (set \<pi>) (set \<sigma>)"
  shows "zag G M v \<pi> \<sigma> = [v]"
  using assms
  by (cases "matching M")
     (auto simp: zag.simps shifts_to_def)

lemma sorted_wrt_arrival_zag:
  assumes "bipartite M (set \<pi>) (set \<sigma>)"
  shows "sorted_wrt (\<lambda>a b. index \<pi> a < index \<pi> b) [x <- zag G M u \<pi> \<sigma>. x \<in> set \<pi>]"
proof (cases "u \<in> set \<pi>")
  case True
  then show ?thesis
  proof (induction "zag G M u \<pi> \<sigma>" arbitrary: u rule: induct_list012)
    case 2
    from this(1)[symmetric] show ?case
      by simp
  next
    case (3 u' v uvs)
    then show ?case
    proof (cases uvs)
      case Nil
      with 3 show ?thesis
        by (metis alt_list_step alt_list_zag assms bipartite_disjointD disjoint_iff filter.simps(1) filter.simps(2) sorted_wrt1)
    next
      case (Cons u'' vus)
      with 3 have uvs_zag: "uvs = zag G M u'' \<pi> \<sigma>"
        by (metis zag_then_zig zig_then_zag)

      with 3 assms have "u'' \<in> set \<pi>"
        by (metis alt_list_step alt_list_zag zag_hdE)

      with 3 assms have "v \<notin> set \<pi>"
        by (metis DiffE bipartite_edgeD(1) local.Cons zag_then_zig zig_matching_edge)

      from 3 have "u' \<in> set \<pi>"
        by (auto elim: zag_symE)

      with 3(3)[symmetric] uvs_zag \<open>v \<notin> set \<pi>\<close> have "[x <- zag G M u \<pi> \<sigma>. x \<in> set \<pi>] = u' # [x <- zag G M u'' \<pi> \<sigma>. x \<in> set \<pi>]"
        by simp

      with 3 uvs_zag \<open>u'' \<in> set \<pi>\<close> show ?thesis
        apply (auto simp flip: successively_conv_sorted_wrt[OF transp_index_less])
        by (metis (no_types, lifting) filter.simps(2) local.Cons successively.simps(3) zag_ConsE zag_increasing_arrival)
    qed
  qed simp
next
  case False
  with assms show ?thesis
    by (simp add: zag_start_wrong_side)
qed

lemma sorted_wrt_arrival_zig:
  assumes "bipartite M (set \<pi>) (set \<sigma>)"
  shows "sorted_wrt (\<lambda>a b. index \<pi> a < index \<pi> b) [x <- zig G M v \<pi> \<sigma>. x \<in> set \<pi>]"
proof (cases "v \<in> set \<sigma>")
  case True
  with assms have "v \<notin> set \<pi>"
    by (auto dest: bipartite_disjointD)

  show ?thesis
  proof (cases "zig G M v \<pi> \<sigma>")
    case (Cons v' uvs)
    then show ?thesis
    proof (cases uvs)
      case (Cons u vus)
      with \<open>zig G M v \<pi> \<sigma> = v' # uvs\<close> have "zig G M v \<pi> \<sigma> = v # zag G M u \<pi> \<sigma>" "{u,v} \<in> M"
        by (metis zig_Cons_zagE zig_then_zag)+

      with \<open>v \<notin> set \<pi>\<close> assms
      show ?thesis
        by (simp add: sorted_wrt_arrival_zag)
    qed simp
  qed simp
next
  case False
  with assms show ?thesis
    by (auto elim!: zig_start_wrong_side[where G = G] dest: bipartite_edgeD)
qed

lemma distinct_zig:
  assumes "bipartite M (set \<pi>) (set \<sigma>)"
  shows "distinct (zig G M v \<pi> \<sigma>)"
proof (cases "v \<in> set \<sigma>")
  case True
  with assms show ?thesis
    by (auto intro!: alt_list_distinct[OF alt_list_zig] intro: sorted_wrt_index_less_distinct sorted_wrt_rank_zig sorted_wrt_arrival_zig dest: bipartite_disjointD)
next
  case False
  with assms show ?thesis
    by (auto elim!: zig_start_wrong_side[where G = G] bipartite_edgeE simp: distinct_length_2_or_more)
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

lemma step_Vs_subset: "x \<in> Vs (step G u \<sigma> M) \<Longrightarrow> x = u \<or> x \<in> set \<sigma> \<or> x \<in> Vs M"
  by (induction G u \<sigma> M rule: step.induct)
     (auto split: if_splits simp: Vs_def)

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

lemma ranking'_Vs_subset: "x \<in> Vs (ranking' G \<pi> \<sigma> M) \<Longrightarrow> x \<in> Vs M \<or> x \<in> set \<pi> \<or> x \<in> set \<sigma>"
  by (induction G \<pi> \<sigma> M rule: ranking'.induct)
     (auto dest: step_Vs_subset)

lemma ranking_Vs_subset: "x \<in> Vs (ranking G \<pi> \<sigma>) \<Longrightarrow> x \<in> set \<pi> \<or> x \<in> set \<sigma>"
  by (auto dest: ranking'_Vs_subset)

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

lemma graph_abs_ranking:
  assumes "graph_abs G"
  shows "graph_abs (ranking G \<pi> \<sigma>)"
  using assms
  by (auto intro: graph_abs_ranking')

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
  shows "e \<in> ranking' G \<pi> \<sigma> M \<Longrightarrow> e \<in> G"
  using assms
  by (induction \<pi> arbitrary: M) (auto simp: step_matches_graph_edge)

lemma subgraph_ranking: "e \<in> ranking G \<pi> \<sigma> \<Longrightarrow> e \<in> G"
  by (auto intro: subgraph_ranking')

lemma bipartite_ranking':
  assumes "bipartite G (set \<pi>) (set \<sigma>)"
  assumes "M \<subseteq> G"
  shows "bipartite (ranking' G \<pi> \<sigma> M) (set \<pi>) (set \<sigma>)"
  using assms
  by (auto intro: bipartite_subgraph dest: subgraph_ranking')

lemma bipartite_ranking:
  assumes "bipartite G (set \<pi>) (set \<sigma>)"
  shows "bipartite (ranking G \<pi> \<sigma>) (set \<pi>) (set \<sigma>)"
  using assms
  by (auto intro: bipartite_ranking')

lemma not_matched_in_prefix:
  assumes "x \<notin> Vs (ranking G \<pi> \<sigma>)"
  assumes "\<pi> = us @ us'"
  shows "x \<notin> Vs (ranking G us \<sigma>)"
  using assms
  by (auto simp: ranking_append dest: ranking_mono_vs)

lemma maximal_ranking_aux:
  assumes "{u,v} \<in> G"
  assumes "u \<in> set \<pi>" "v \<in> set \<sigma>"
  assumes "set \<pi> \<inter> set \<sigma> = {}"
  assumes "u \<notin> Vs (ranking G \<pi> \<sigma>)" "v \<notin> Vs (ranking G \<pi> \<sigma>)"
  shows False
proof -
  from \<open>u \<in> set \<pi>\<close> obtain us us' where split_pi: "\<pi> = us @ u # us'"
    by (auto dest: split_list)

  with \<open>u \<notin> Vs (ranking G \<pi> \<sigma>)\<close> \<open>v \<notin> Vs (ranking G \<pi> \<sigma>)\<close> have "u \<notin> Vs (ranking G us \<sigma>)" "v \<notin> Vs (ranking G us \<sigma>)"
    by (auto dest: not_matched_in_prefix)

  with \<open>{u,v} \<in> G\<close> \<open>u \<in> set \<pi>\<close> \<open>v \<in> set \<sigma>\<close> obtain v' where "{u,v'} \<in> step G u \<sigma> (ranking G us \<sigma>)"
    by (auto dest: step_matches_if_possible)

  with split_pi have "{u,v'} \<in> ranking G \<pi> \<sigma>"
    by (simp add: ranking_append ranking_mono)

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

lemma ranking_matched_together:
  assumes bipartite: "bipartite G (set \<pi>) (set \<sigma>)"
  assumes "{u,v} \<in> ranking G \<pi> \<sigma>"
  assumes "u \<in> set \<pi>" "u \<notin> set us" "\<pi> = us @ us'"
  shows "v \<notin> Vs (ranking G us \<sigma>)"
proof
  assume "v \<in> Vs (ranking G us \<sigma>)"
  then obtain u' where u': "{u',v} \<in> ranking G us \<sigma>"
    by (smt (verit, del_insts) More_Graph.bipartite_def assms(1) insert_commute insert_iff singletonD subgraph_ranking vs_member)

  with \<open>\<pi> = us @ us'\<close> have "{u',v} \<in> ranking G \<pi> \<sigma>"
    by (simp add: ranking_append ranking_mono)

  from bipartite \<open>u \<notin> set us\<close> \<open>u \<in> set \<pi>\<close> have "u \<notin> Vs (ranking G us \<sigma>)"
    by (auto dest: ranking_Vs_subset bipartite_disjointD)

  with u' have "u \<noteq> u'" by auto

  with bipartite \<open>{u,v} \<in> ranking G \<pi> \<sigma>\<close> \<open>{u',v} \<in> ranking G \<pi> \<sigma>\<close> show False
    by (auto dest!: bipartite_disjointD dest: matching_ranking the_match)
qed

lemma ranking_lowest_free_rank_match:
  assumes bipartite: "bipartite G (set \<pi>) (set \<sigma>)"
  assumes "{u,v} \<in> ranking G \<pi> \<sigma>"
  assumes "{u,v'} \<in> G"
  assumes v'_before_v: "index \<sigma> v' < index \<sigma> v"
  shows "\<exists>u'. {u',v'} \<in> ranking G \<pi> \<sigma> \<and> index \<pi> u' < index \<pi> u"
proof (rule ccontr)
  assume contr: "\<nexists>u'. {u', v'} \<in> ranking G \<pi> \<sigma> \<and> index \<pi> u' < index \<pi> u"

  from \<open>{u,v} \<in> ranking G \<pi> \<sigma>\<close> have "{u,v} \<in> G"
    by (auto intro: subgraph_ranking)

  from v'_before_v have "v' \<in> set \<sigma>"
    by (auto dest: index_less_in_set)

  with bipartite \<open>{u,v'} \<in> G\<close> have "u \<in> set \<pi>"
    by (auto dest: bipartite_edgeD edge_commute)

  with bipartite \<open>{u,v} \<in> ranking G \<pi> \<sigma>\<close> have "v \<in> set \<sigma>"
    by (auto dest: bipartite_edgeD bipartite_ranking)

  from \<open>u \<in> set \<pi>\<close> obtain us us' where split_pi: "\<pi> = us @ u # us' \<and> u \<notin> set us"
    by (auto dest: split_list_first)

  with bipartite \<open>u \<in> set \<pi>\<close> \<open>{u,v} \<in> G\<close> have "u \<notin> Vs (ranking G us \<sigma>)"
    by (auto dest: ranking_Vs_subset bipartite_edgeD)

  then have no_v': "\<And>v'. {u,v'} \<notin> ranking G us \<sigma>"
    by (auto dest: edges_are_Vs)

  from bipartite \<open>{u,v} \<in> ranking G \<pi> \<sigma>\<close> \<open>u \<in> set \<pi>\<close> split_pi have "v \<notin> Vs (ranking G us \<sigma>)"
    by (intro ranking_matched_together) auto

  with \<open>u \<notin> Vs (ranking G us \<sigma>)\<close> \<open>v \<in> set \<sigma>\<close> \<open>{u,v} \<in> G\<close>
  obtain v'' where v'': "{u,v''} \<in> step G u \<sigma> (ranking G us \<sigma>)"
    by (auto dest: step_matches_if_possible)

  show False
  proof (cases "v = v''")
    case True

    from v'' no_v' have v_lowest_rank: "\<forall>v'\<in>set \<sigma> \<inter> {v''. {u, v''} \<in> G} - Vs (ranking G us \<sigma>) - {v''}. index \<sigma> v'' < index \<sigma> v'"
      by (auto elim!: edge_matched_in_stepE simp: doubleton_eq_iff)

    from v'_before_v have "v \<noteq> v'" by blast

    have "v' \<notin> Vs (ranking G us \<sigma>)"
    proof
      assume "v' \<in> Vs (ranking G us \<sigma>)"
      then obtain e where "e \<in> ranking G us \<sigma>" "v' \<in> e"
        by (auto elim: vs_member_elim)

      with \<open>v' \<in> set \<sigma>\<close> obtain u' where "e = {u',v'}" "u' \<in> set us"
        by (smt (verit, ccfv_threshold) bipartite bipartite_disjointD bipartite_edgeE disjoint_iff_not_equal edges_are_Vs(1) insert_iff ranking_Vs_subset singletonD subgraph_ranking)

      with split_pi have "index \<pi> u' < index \<pi> u"
        by (auto simp: index_append)

      with contr split_pi \<open>e \<in> ranking G us \<sigma>\<close> \<open>e = {u',v'}\<close> show False
        using ranking_append ranking_mono by blast
    qed

    with True \<open>v' \<in> set \<sigma>\<close> \<open>{u,v'} \<in> G\<close> \<open>v \<noteq> v'\<close> have "v'\<in>set \<sigma> \<inter> {v''. {u, v''} \<in> G} - Vs (ranking G us \<sigma>) - {v''}"
      by blast

    with True v_lowest_rank v'_before_v show ?thesis
      by (meson not_less_iff_gr_or_eq)
  next
    case False

    from split_pi have "ranking G \<pi> \<sigma> = ranking' G us' \<sigma> (step G u \<sigma> (ranking G us \<sigma>))"
      by (simp add: ranking_foldl)

    with \<open>{u,v''} \<in> step G u \<sigma> (ranking G us \<sigma>)\<close> have "{u,v''} \<in> ranking G \<pi> \<sigma>"
      by (auto intro: ranking_mono)

    with bipartite False \<open>{u,v} \<in> ranking G \<pi> \<sigma>\<close> the_match' show ?thesis
      by (metis bipartite_disjointD matching_ranking)
  qed
qed

lemma ranking_earliest_match:
  assumes bipartite: "bipartite G (set \<pi>) (set \<sigma>)"
  assumes "{u,v} \<in> ranking G \<pi> \<sigma>"
  assumes "{u',v} \<in> G"
  assumes u'_before_u: "index \<pi> u' < index \<pi> u"
  shows "\<exists>v'. {u',v'} \<in> ranking G \<pi> \<sigma> \<and> index \<sigma> v' < index \<sigma> v"
proof (rule ccontr)
  assume contr: "\<nexists>v'. {u',v'} \<in> ranking G \<pi> \<sigma> \<and> index \<sigma> v' < index \<sigma> v"

  from u'_before_u have "u' \<in> set \<pi>"
    by (auto intro: index_less_in_set)

  with bipartite \<open>{u',v} \<in> G\<close> have "v \<in> set \<sigma>"
    by (auto dest: bipartite_edgeD)

  with bipartite \<open>{u,v} \<in> ranking G \<pi> \<sigma>\<close> have "u \<in> set \<pi>"
    by (auto dest: bipartite_ranking bipartite_edgeD)

  from \<open>u' \<in> set \<pi>\<close> obtain us us' where split_pi: "\<pi> = us @ u' # us' \<and> u' \<notin> set us"
    by (auto dest: split_list_first)

  with u'_before_u have "u \<notin> set us"
    by (auto simp: index_append index_le_size leD)

  with bipartite \<open>u \<in> set \<pi>\<close> have  "u \<notin> Vs (ranking G us \<sigma>)"
    by (auto dest: bipartite_disjointD ranking_Vs_subset)

  with bipartite \<open>{u,v} \<in> ranking G \<pi> \<sigma>\<close> \<open>u \<in> set \<pi>\<close> \<open>u \<notin> set us\<close> split_pi have "v \<notin> Vs (ranking G us \<sigma>)"
    by (meson ranking_matched_together)

  from bipartite \<open>u' \<in> set \<pi>\<close> split_pi have "u' \<notin> Vs (ranking G us \<sigma>)"
    by (auto dest: bipartite_disjointD ranking_Vs_subset)

  with \<open>v \<notin> Vs (ranking G us \<sigma>)\<close> \<open>v \<in> set \<sigma>\<close> \<open>{u',v} \<in> G\<close>
  obtain v' where v': "{u',v'} \<in> step G u' \<sigma> (ranking G us \<sigma>)"
    by (auto dest: step_matches_if_possible)

  show False
  proof (cases "v' = v")
    case True
    from u'_before_u have "u \<noteq> u'" by blast

    from v' split_pi have "{u',v'} \<in> ranking G \<pi> \<sigma>"
      by (auto simp: ranking_append dest: ranking_mono)

    with True bipartite \<open>{u,v} \<in> ranking G \<pi> \<sigma>\<close> \<open>u \<noteq> u'\<close> show ?thesis
      by (metis bipartite_disjointD matching_ranking the_match)
  next
    case False

    from \<open>u' \<notin> Vs (ranking G us \<sigma>)\<close> have "{u',v'} \<notin> ranking G us \<sigma>"
      by (auto dest: edges_are_Vs)

    with v' have v'_lowest_rank: "\<forall>v\<in>set \<sigma> \<inter> {v''. {u', v''} \<in> G} - Vs (ranking G us \<sigma>) - {v'}. index \<sigma> v' < index \<sigma> v"
      by (auto elim!: edge_matched_in_stepE simp: doubleton_eq_iff)

    from False \<open>v \<in> set \<sigma>\<close> \<open>{u',v} \<in> G\<close> \<open>v \<notin> Vs (ranking G us \<sigma>)\<close>
    have "v \<in> set \<sigma> \<inter> {v''. {u',v''} \<in> G} - Vs (ranking G us \<sigma>) - {v'}" by blast

    with v'_lowest_rank have "index \<sigma> v' < index \<sigma> v" by blast

    with contr split_pi \<open>{u',v'} \<in> step G u' \<sigma> (ranking G us \<sigma>)\<close> show ?thesis
      by (auto simp: ranking_append dest: ranking_mono)
  qed
qed

lemma ranking_matching_ranking:
  "bipartite G (set \<pi>) (set \<sigma>) \<Longrightarrow> ranking_matching G (ranking G \<pi> \<sigma>) \<pi> \<sigma>"
  unfolding ranking_matching_def
  by (auto dest: bipartite_disjointD ranking_lowest_free_rank_match ranking_earliest_match
           intro: matching_ranking subgraph_ranking maximal_ranking)

lemma ranking_commute:
  assumes "bipartite G (set \<pi>) (set \<sigma>)"
  shows "ranking G \<pi> \<sigma> = ranking G \<sigma> \<pi>"
  using assms
  by (auto intro!: ranking_matching_unique intro: ranking_matching_commute dest: ranking_matching_ranking bipartite_commute)


subsection \<open>Removing vertices\<close>
lemma step_u_not_in_graph:
  "u \<notin> Vs G \<Longrightarrow> step G u \<sigma> M = M"
  by (induction G u \<sigma> M rule: step.induct)
     (auto dest: edges_are_Vs)

lemma ranking'_remove_vertices_graph_remove_vertices_arrival:
  "ranking' (G \<setminus> X) (\<pi> \<setminus> X) \<sigma> M = ranking' (G \<setminus> X) \<pi> \<sigma> M"
  by (induction "G \<setminus> X" \<pi> \<sigma> M rule: ranking'.induct)
     (auto simp: remove_vertices_list_def remove_vertices_not_vs step_u_not_in_graph)

lemma ranking_remove_vertices_graph_remove_vertices_arrival:
  "ranking (G \<setminus> X) (\<pi> \<setminus> X) \<sigma> = ranking (G \<setminus> X) \<pi> \<sigma>"
  using ranking'_remove_vertices_graph_remove_vertices_arrival
  by blast

lemma step_remove_vertices_graph_remove_vertices_rank:
  "step (G \<setminus> X) u (\<sigma> \<setminus> X) M = step (G \<setminus> X) u \<sigma> M"
  by (induction "G \<setminus> X" u \<sigma> M rule: step.induct)
     (simp_all add: remove_vertices_list_def remove_vertices_graph_def)

lemma ranking'_remove_vertices_graph_remove_vertices_rank:
  "ranking' (G \<setminus> X) \<pi> (\<sigma> \<setminus> X) M = ranking' (G \<setminus> X) \<pi> \<sigma> M"
  by (induction "G \<setminus> X" \<pi> \<sigma> M rule: ranking'.induct)
     (simp_all add: step_remove_vertices_graph_remove_vertices_rank)

lemma ranking_remove_vertices_graph_remove_vertices_rank:
  "ranking (G \<setminus> X) \<pi> (\<sigma> \<setminus> X) = ranking (G \<setminus> X) \<pi> \<sigma>"
  using ranking'_remove_vertices_graph_remove_vertices_rank
  by blast

lemma step_remove_unmatched_vertex_same:
  assumes "x \<notin> Vs (step G u \<sigma> M)"
  shows "step G u \<sigma> M = step (G \<setminus> {x}) u \<sigma> M"
  using assms
  apply (induction G u \<sigma> M rule: step.induct)
   apply simp_all
  by (smt (verit, ccfv_SIG) disjoint_insert(1) inf_bot_right insertCI mem_Collect_eq remove_vertices_graph_def vs_member)

lemma ranking_remove_unmatched_vertex_same:
  assumes "x \<notin> Vs (ranking' G \<pi> \<sigma> M)"
  shows "ranking' G \<pi> \<sigma> M = ranking' (G \<setminus> {x}) \<pi> \<sigma> M"
  using assms
  apply (induction G \<pi> \<sigma> M rule: ranking'.induct)
   apply simp_all
  by (metis ranking_mono_vs step_remove_unmatched_vertex_same)


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
proof (induction G M v \<pi> \<sigma> and G M u \<pi> \<sigma> rule: zig_zag_induct)
  case (1 G M v \<pi> \<sigma> u)
  then have "u \<in> set \<pi>"
    by (auto dest: bipartite_edgeD)

  from \<open>matching M\<close> have "matching (M \<setminus> X)"
    by (auto intro: matching_remove_vertices)

  from "1.prems" \<open>{u,v} \<in> M\<close> \<open>matching M\<close> have "u \<notin> X"
    by (auto simp: the_match')

  from "1.prems" have "v \<notin> X"
    by (auto dest!: bipartite_disjointD)

  with \<open>{u,v} \<in> M\<close> \<open>u \<notin> X\<close> have "{u,v} \<in> M \<setminus> X"
    by (auto intro: in_remove_verticesI)

  with 1 \<open>matching (M \<setminus> X)\<close> \<open>u \<in> set \<pi>\<close> show ?case
    by (auto simp: zig.simps the_match' the_match)
next
  case (2 G M v \<pi> \<sigma>)
  then have "matching (M \<setminus> X)" "\<nexists>u. {u,v} \<in> M \<setminus> X"
    by (auto dest: matching_remove_vertices remove_vertices_subgraph')

  with 2 show ?case
    by (auto simp: zig.simps)
next
  case (4 G M u \<pi> \<sigma>)

  have uv: "\<And>v. {u,v} \<in> M \<Longrightarrow> {u,v} \<in> M \<setminus> X"
  proof (intro in_remove_verticesI, simp)
    fix v
    assume "{u,v} \<in> M"

    with "4.prems" have "u \<notin> X"
      by (auto simp: the_match)

    from 4 \<open>{u,v} \<in> M\<close> have "v \<notin> X"
      by (auto dest: bipartite_edgeD)

    with \<open>u \<notin> X\<close> show "{u,v} \<inter> X = {}"
      by blast
  qed

  from \<open>matching M\<close> have "matching (M \<setminus> X)"
    by (auto intro: matching_remove_vertices)

  from zag_casesE[of u M G \<pi> \<sigma>]
  show ?case
  proof cases
    case 1
    then obtain v v' where vv': "{u,v} \<in> M" "shifts_to G M u v v' \<pi> \<sigma>" by blast

    then have "{u,v} \<in> M \<setminus> X"
      by (auto intro: uv)

    from vv' have v': "v' \<in> set \<sigma>" "index \<sigma> v < index \<sigma> v'"
      by (auto simp add: shifts_to_def)

    from "4.prems" vv' have "u \<notin> X"
      by (auto simp: the_match)

    from "4.prems" vv' \<open>u \<notin> X\<close> have "shifts_to (G \<setminus> X) (M \<setminus> X) u v v' \<pi> \<sigma>"
      by (auto intro!: remove_online_vertices_shifts_to_same dest: bipartite_disjointD simp: the_match')

    with 4 vv' v' \<open>matching (M \<setminus> X)\<close> \<open>{u,v} \<in> M \<setminus> X\<close> show ?thesis
      apply (auto simp: zag.simps the_match the_match' the_shifts_to)
      by (meson order.strict_trans)
  next
    case 2
    then obtain v where v: "{u,v} \<in> M" "\<nexists>v'. shifts_to G M u v v' \<pi> \<sigma>" by blast

    then have "\<nexists>v'. shifts_to (G \<setminus> X) (M \<setminus> X) u v v' \<pi> \<sigma>"
      using 2 remove_online_vertices_before_shifts_to_mono[OF bipartite_disjointD[OF \<open>bipartite M (set \<pi>) (set \<sigma>)\<close>]
          \<open>X \<subseteq> set \<pi>\<close> \<open>matching M\<close> 4(4) _] \<open>matching M\<close>
      by (auto simp: the_match') blast

    with v uv[OF v(1)] \<open>matching M\<close> \<open>matching (M \<setminus> X)\<close> show ?thesis
      by (auto simp: zag.simps the_match' the_shifts_to)
  next
    case 3
    with \<open>matching M\<close> \<open>matching (M \<setminus> X)\<close> show ?thesis
      by (auto simp: zag.simps dest: remove_vertices_subgraph')
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
proof (induction G M v \<pi> \<sigma> and G M u \<pi> \<sigma> rule: zig_zag_induct)
  case (1 G M v \<pi> \<sigma> u)

  then have "matching (M \<setminus> X)"
    by (simp add: matching_remove_vertices)

  from \<open>v \<in> set \<sigma>\<close> \<open>\<forall>x\<in>X. index \<sigma> x < index \<sigma> v\<close> have "v \<notin> X" by blast

  from \<open>v \<in> set \<sigma>\<close> \<open>{u,v} \<in> M\<close> \<open>bipartite M (set \<pi>) (set \<sigma>)\<close> have "u \<in> set \<pi>"
    unfolding bipartite_def
    by fast

  with \<open>X \<subseteq> set \<sigma>\<close> \<open>bipartite M (set \<pi>) (set \<sigma>)\<close> have "u \<notin> X"
    by (auto dest: bipartite_disjointD)

  with \<open>{u,v} \<in> M\<close> \<open>v \<notin> X\<close> have "{u,v} \<in> M \<setminus> X"
    by (auto intro: in_remove_verticesI)

  with 1 \<open>matching (M \<setminus> X)\<close> \<open>{u,v} \<in> M \<setminus> X\<close> \<open>u \<in> set \<pi>\<close> show ?case
    by (auto simp: zig.simps simp: the_match' the_match)
next
  case (2 G M v \<pi> \<sigma>)
    then have "\<nexists>u. {u,v} \<in> M \<setminus> X"
      using remove_vertices_subgraph by blast

    with 2 \<open>matching M\<close> matching_remove_vertices[OF \<open>matching M\<close>] show ?case
      by (auto simp: zig.simps)
next
  case (4 G M u \<pi> \<sigma>)

  then have "u \<notin> X"
    by (auto dest!: bipartite_disjointD)

  have uv: "\<And>v. {u,v} \<in> M \<Longrightarrow> {u,v} \<in> M \<setminus> X"
  proof (rule in_remove_verticesI, simp)
    fix v
    assume "{u,v} \<in> M"

    with "4.prems" have "v \<notin> X"
      by (auto simp: the_match')

    with \<open>u \<notin> X\<close> show "{u,v} \<inter> X = {}"
      by blast
  qed

  from \<open>matching M\<close> have "matching (M \<setminus> X)"
    by (simp add: matching_remove_vertices)

  from zag_casesE[of u M G \<pi> \<sigma>]
  show ?case 
  proof cases
    case 1
    then obtain v v' where vv': "{u,v} \<in> M" "shifts_to G M u v v' \<pi> \<sigma>" by blast

    then have v': "v' \<in> set \<sigma>" "index \<sigma> v < index \<sigma> v'"
      by (auto simp: shifts_to_def)

    from vv' have "{u,v} \<in> M \<setminus> X"
      by (auto intro: uv)

    from "4.prems" vv' have "shifts_to (G \<setminus> X) (M \<setminus> X) u v v' \<pi> \<sigma>"
      by (auto intro!: remove_offline_vertices_before_shifts_to_same' dest: bipartite_disjointD simp: the_match')

    with 4 vv' v' \<open>matching (M \<setminus> X)\<close> \<open>{u,v} \<in> M \<setminus> X\<close> \<open>v' \<in> set \<sigma>\<close> show ?thesis
      apply (auto simp: zag.simps simp: the_match the_match' the_shifts_to)
      by (meson order.strict_trans)
  next
    case 2
    then obtain v where v: "{u,v} \<in> M" "\<nexists>v'. shifts_to G M u v v' \<pi> \<sigma>" by blast

    with "4.prems" have "\<nexists>v'. shifts_to (G \<setminus> X) (M \<setminus> X) u v v' \<pi> \<sigma>"
      using remove_offline_vertices_before_shifts_to_mono[OF bipartite_disjointD[OF \<open>bipartite M (set \<pi>) (set \<sigma>)\<close>]
          \<open>X \<subseteq> set \<sigma>\<close>]
      by (auto simp: the_match') blast
      
    with v uv[OF v(1)] \<open>matching M\<close> \<open>matching (M \<setminus> X)\<close> show ?thesis
      by (auto simp: zag.simps the_match')
  next
    case 3
    with \<open>matching M\<close> \<open>matching (M \<setminus> X)\<close> show ?thesis
      by (auto simp: zag.simps dest: remove_vertices_subgraph')
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

lemma remove_offline_vertex_diff_is_zig:
  assumes "ranking_matching G M \<pi> \<sigma>"
  assumes "ranking_matching (G \<setminus> {x}) M' \<pi> \<sigma>"
  assumes "x \<in> set \<sigma>"
  shows "M \<oplus> M' = set (edges_of_path (zig G M x \<pi> \<sigma>))"
  using assms
proof (induction "card G" arbitrary: G M M' \<pi> \<sigma> x rule: less_induct)
  case less

  then have "matching M" by (auto dest: ranking_matchingD maximal_matchingD)

  consider (matched) "x \<in> Vs M" | (unmatched) "x \<notin> Vs M" by blast
  then show ?case
  proof cases
    case matched
    then obtain u where "{u,x} \<in> M"
      by (meson edge_commute graph_abs_no_edge_no_vertex less.prems(1) ranking_matchingD)

    with \<open>x \<in> set \<sigma>\<close> \<open>ranking_matching G M \<pi> \<sigma>\<close> have "u \<in> set \<pi>"
      by (auto dest: ranking_matching_bipartite_edges')

    have "{u,x} \<notin> G \<setminus> {x}"
      by (auto dest: edges_are_Vs intro: remove_vertices_not_vs')

    from \<open>{u,x} \<in> M\<close> \<open>ranking_matching G M \<pi> \<sigma>\<close> have rm_Gxu: "ranking_matching (G \<setminus> {x} \<setminus> {u}) (M \<setminus> {u,x}) \<sigma> \<pi>"
      by (auto simp: remove_remove_union intro: remove_edge_ranking_matching ranking_matching_commute)

    from \<open>{u,x} \<in> M\<close> \<open>{u,x} \<notin> G \<setminus> {x}\<close> \<open>ranking_matching G M \<pi> \<sigma>\<close> have "card (G \<setminus> {x}) < card G"
      by (auto intro!: psubset_card_mono dest: ranking_matchingD remove_vertices_subgraph' elim: graph_abs.finite_E)


    from \<open>{u,x} \<in> M\<close> \<open>{u,x} \<notin> G \<setminus> {x}\<close> have "M \<oplus> M' = insert {u,x} (M' \<oplus> (M \<setminus> {u,x}))"
      by (smt (verit, ccfv_threshold) Diff_insert0 Un_insert_right \<open>matching M\<close> insert_Diff insert_Diff_if less.prems(2) ranking_matchingD remove_edge_matching subsetD sym_diff_sym symmetric_diff_def)
 
    also have "\<dots> = insert {u,x} (set (edges_of_path (zig (G \<setminus> {x}) M' u \<sigma> \<pi>)))"
      using less.hyps[OF \<open>card (G \<setminus> {x}) < card G\<close> ranking_matching_commute[OF less.prems(2)] rm_Gxu \<open>u \<in> set \<pi>\<close>]
      by simp

    also have "\<dots> = insert {u,x} (set (edges_of_path (zag G M u \<pi> \<sigma>)))"
      using ranking_matching_zig_zag_eq[OF \<open>{u,x} \<in> M\<close> \<open>x \<in> set \<sigma>\<close> \<open>ranking_matching G M \<pi> \<sigma>\<close> ranking_matching_commute[OF\<open>ranking_matching (G \<setminus> {x}) M' \<pi> \<sigma>\<close>]]
      by simp

    also have "\<dots> = set (edges_of_path (x # zag G M u \<pi> \<sigma>))"
      by (smt (verit, ccfv_SIG) \<open>matching M\<close> edges_of_path.elims insert_commute list.inject list.simps(15) list.simps(3) zag_ConsE zag_NilE)

    also have "\<dots> = set (edges_of_path (zig G M x \<pi> \<sigma>))"
      using \<open>matching M\<close> \<open>{u,x} \<in> M\<close>
      by (auto simp: zig.simps dest: the_match)

    finally show ?thesis .
  next
    case unmatched
    then have "\<nexists>u. {u,x} \<in> M"
      by (auto dest: edges_are_Vs)

    from unmatched less.prems have "M = M'"
      by (metis ranking_matchingD ranking_matching_ranking ranking_matching_unique ranking_remove_unmatched_vertex_same)

    with less.prems \<open>\<nexists>u. {u,x} \<in> M\<close> \<open>matching M\<close> show ?thesis
      by (auto simp: zig.simps)
  qed
qed

lemma remove_online_vertex_diff_is_zig:
  assumes "ranking_matching G M \<pi> \<sigma>"
  assumes "ranking_matching (G \<setminus> {x}) M' \<pi> \<sigma>"
  assumes "x \<in> set \<pi>"
  shows "M \<oplus> M' = set (edges_of_path (zig G M x \<sigma> \<pi>))"
  using assms
  by (meson ranking_matching_commute remove_offline_vertex_diff_is_zig)

definition remove_vertex_path :: "'a graph \<Rightarrow> 'a graph \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "remove_vertex_path G M x \<pi> \<sigma> \<equiv> if x \<in> set \<sigma> then zig G M x \<pi> \<sigma> else zig G M x \<sigma> \<pi>"

lemma remove_vertex_path_offline_zig:
  "x \<in> set \<sigma> \<Longrightarrow> remove_vertex_path G M x \<pi> \<sigma> = zig G M x \<pi> \<sigma>"
  unfolding remove_vertex_path_def
  by simp

lemma remove_vertex_path_not_offline_zig:
  "x \<notin> set \<sigma> \<Longrightarrow> remove_vertex_path G M x \<pi> \<sigma> = zig G M x \<sigma> \<pi>"
  unfolding remove_vertex_path_def
  by simp

lemma rev_alt_path_remove_vertex_path: "rev_alt_path M (remove_vertex_path G M x \<pi> \<sigma>)"
  unfolding remove_vertex_path_def
  by (auto intro: rev_alt_path_zig_edges)

lemma remove_vertex_diff_is_zig:
  assumes "ranking_matching G M \<pi> \<sigma>"
  assumes "ranking_matching (G \<setminus> {x}) M' \<pi> \<sigma>"
  shows "M \<oplus> M' = set (edges_of_path (remove_vertex_path G M x \<pi> \<sigma>))"
  using assms
proof -
  from \<open>ranking_matching G M \<pi> \<sigma>\<close> consider (offline) "x \<in> set \<sigma>" | (online) "x \<in> set \<pi>" | (no_vertex) "x \<notin> Vs G"
    by (smt (verit, ccfv_SIG) bipartite_edgeE insert_iff ranking_matchingD singletonD vs_member)

  then show ?thesis
  proof cases
    case offline
    with assms show ?thesis
      by (auto dest: remove_offline_vertex_diff_is_zig simp: remove_vertex_path_offline_zig)
  next
    case online
    with assms have "x \<notin> set \<sigma>"
      by (auto dest!: ranking_matchingD simp: bipartite_def)

    with assms online show ?thesis
      by (auto dest: remove_online_vertex_diff_is_zig simp: remove_vertex_path_not_offline_zig)
  next
    case no_vertex
    then show ?thesis
      unfolding remove_vertex_path_def
      by (smt (verit, ccfv_SIG) Ranking2.no_matching_zig assms(1) assms(2) edges_of_path.simps(2) insertCI ranking_matchingD ranking_matching_unique remove_vertex_not_in_graph set_empty subsetD symm_diff_empty vs_member zig.simps(1))
  qed
qed

lemma remove_vertex_diff_is_zigE:
  assumes "ranking_matching G M \<pi> \<sigma>"
  assumes "ranking_matching (G \<setminus> {x}) M' \<pi> \<sigma>"
  obtains "M \<oplus> M' = set (edges_of_path (remove_vertex_path G M x \<pi> \<sigma>))"
  using assms
  by (auto dest: remove_vertex_diff_is_zig)

lemma remove_vertex_alt_path:
  assumes "ranking_matching G M \<pi> \<sigma>"
  assumes "ranking_matching (G \<setminus> {x}) M' \<pi> \<sigma>"
  shows "alt_path M' (remove_vertex_path G M x \<pi> \<sigma>)"
  using assms
  by (auto intro: rev_alt_path_sym_diff_alt_path[OF _ _ remove_vertex_diff_is_zig]
                  rev_alt_path_remove_vertex_path
           dest: ranking_matchingD)

lemma remove_vertex_path_hd:
  shows "hd (remove_vertex_path G M x \<pi> \<sigma>) = x"
  unfolding remove_vertex_path_def
  by (auto simp: hd_zig)

lemma remove_vertex_path_not_augmenting:
  shows "augmenting_path M (remove_vertex_path G M x \<pi> \<sigma>) \<Longrightarrow> False"
  unfolding remove_vertex_path_def
  by (auto split: if_splits dest: zig_not_augmenting)

lemma distinct_remove_vertex_path:
  assumes "bipartite M (set \<pi>) (set \<sigma>)"
  shows "distinct (remove_vertex_path G M x \<pi> \<sigma>)"
  using assms
  unfolding remove_vertex_path_def
  by (auto intro: distinct_zig dest: bipartite_commute)

end
