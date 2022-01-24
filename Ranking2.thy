theory Ranking2
  imports
    More_Graph
    "List-Index.List_Index"
begin

sledgehammer_params [provers = e z3 spass cvc4 vampire]

type_synonym 'a graph = "'a set set"

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

definition ranking_matching :: "'a graph \<Rightarrow> 'a graph \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "ranking_matching G M \<pi> \<sigma> \<equiv> matching M \<and> graph_abs G \<and>
    (\<forall>u\<in>Vs M. \<forall>v\<in>Vs M. \<forall>v'\<in>Vs G. ({u,v}\<in>M \<and> {u,v'}\<in>G \<and> index \<sigma> v' < index \<sigma> v) \<longrightarrow> (\<exists>u'. {u',v'}\<in>M \<and> index \<pi> u' < index \<pi> u))"

lemma ranking_matchingD:
  assumes "ranking_matching G M \<pi> \<sigma>"
  shows "matching M" "graph_abs G"
  using assms
  unfolding ranking_matching_def
  by blast+

abbreviation "ranking G \<pi> \<sigma> \<equiv> ranking' G \<pi> \<sigma> {}"

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


lemma graph_abs_subgraph:
  "graph_abs G \<Longrightarrow> G' \<subseteq> G \<Longrightarrow> graph_abs G'"
  unfolding graph_abs_def
  by (auto dest: Vs_subset intro: finite_subset)

lemma graph_abs_remove_vertices:
  "graph_abs G \<Longrightarrow> graph_abs (G \<setminus> X)"
  by (simp add: graph_abs_subgraph remove_vertices_graph_def)


lemma ranking_matching_remove_vertices:
  "ranking_matching G M \<pi> \<sigma> \<Longrightarrow> ranking_matching (G \<setminus> X) M \<pi> \<sigma>"
  unfolding ranking_matching_def
  by (auto intro: graph_abs_remove_vertices dest!: remove_vertices_subgraph_Vs remove_vertices_subgraph')

lemma remove_remove_union: "G \<setminus> X \<setminus> Y = G \<setminus> X \<union> Y"
  unfolding remove_vertices_graph_def by blast

definition remove_vertices_rank :: "'a list \<Rightarrow> 'a set \<Rightarrow> 'a list" (infix "\<setminus>" 60) where
  "\<sigma> \<setminus> X \<equiv> [v <- \<sigma>. v \<notin> X]"

lemma remove_vertices_not_in_rank:
  "v \<in> X \<Longrightarrow> v \<notin> set (\<sigma> \<setminus> X)"
  unfolding remove_vertices_rank_def
  by simp

lemma remove_vertices_mono:
  "X \<subseteq> X' \<Longrightarrow> e \<in> G \<setminus> X' \<Longrightarrow> e \<in> G \<setminus> X"
  unfolding remove_vertices_graph_def by blast

lemma remove_vertices_mono':
  "X \<subseteq> X' \<Longrightarrow> G \<setminus> X' \<subseteq> G \<setminus> X"
  by (auto dest: remove_vertices_mono)


definition "shifts_to G M u v v' \<sigma> \<pi> \<equiv> 
  \<comment> \<open>v' comes after v and there's an edge to u\<close>
  u \<in> set \<pi> \<and> v' \<in> set \<sigma> \<and> index \<sigma> v < index \<sigma> v' \<and> {u,v'} \<in> G \<and>
  \<comment> \<open>but v' is not matched to some u' before u\<close>
    (\<nexists>u'. index \<pi> u' < index \<pi> u \<and> {u',v'} \<in> M) \<and>
  \<comment> \<open>every other vertex between v and v' is not connected to u or matched to some u' before u\<close>
    (\<forall>v''. (index \<sigma> v < index \<sigma> v'' \<and> index \<sigma> v'' < index \<sigma> v') \<longrightarrow>
      ({u,v''} \<notin> G \<or> (\<exists>u'. index \<pi> u' < index \<pi> u \<and> {u',v''} \<in> M)))"

function zig :: "'a graph \<Rightarrow> 'a graph \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
and zag :: "'a graph \<Rightarrow> 'a graph \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  proper_zig: "zig G M v \<sigma> \<pi> = v # (
                    if \<exists>u. {u,v} \<in> M 
                    then zag G M (THE u. {u,v} \<in> M) \<sigma> \<pi>
                    else [])" if "matching M"
| no_matching_zig: "zig G M v \<sigma> \<pi> = []" if "\<not>matching M"

| proper_zag: "zag G M u \<sigma> \<pi> =  u # (if \<exists>v. {u,v} \<in> M 
                      then 
                      (let v = THE v. {u,v} \<in> M in (
                        if \<exists>v'. shifts_to G M u v v' \<sigma> \<pi>
                        then zig G M (THE v'. shifts_to G M u v v' \<sigma> \<pi>) \<sigma> \<pi>
                        else [])
                      )
                      else []
                    )" if "matching M"
| no_matching_zag: "zag G M u \<sigma> \<pi> = []" if "\<not>matching M"
  by auto (smt (z3) prod_cases5 sum.collapse)

definition zig_zag_relation where
  "zig_zag_relation \<equiv> 
    {(Inr (G, M, u, \<sigma>, \<pi>), Inl (G, M, v, \<sigma>, \<pi>)) | (G :: 'a graph) M u v \<sigma> \<pi>. matching M \<and> {u,v} \<in> M \<and> ((\<exists>v'. shifts_to G M u v v' \<sigma> \<pi>) \<longrightarrow> index \<sigma> v < index \<sigma> (THE v'. shifts_to G M u v v' \<sigma> \<pi>))} \<union>
    {(Inl (G, M, v', \<sigma>, \<pi>), Inr (G, M, u, \<sigma>, \<pi>)) | (G :: 'a graph) M u v' \<sigma> \<pi>. matching M \<and> (\<exists>v. {u,v} \<in> M \<and> shifts_to G M u (THE v. {u,v} \<in> M) v' \<sigma> \<pi>) \<and> index \<sigma> (THE v. {u,v} \<in> M) < index \<sigma> v'}"


lemma the_match: "matching M \<Longrightarrow> {u,v} \<in> M \<Longrightarrow> (THE u. {u,v} \<in> M) = u"
  apply (auto intro!: the_equality )
  by (metis doubleton_eq_iff insertI1 matching_unique_match)

lemma the_match': "matching M \<Longrightarrow> {u,v} \<in> M \<Longrightarrow> (THE v. {u,v} \<in> M) = v"
  apply (auto intro!: the_equality)
  by (metis (mono_tags, lifting) insert_commute the_match)

lemma shifts_to_only_from_input:
  assumes "shifts_to G M u v v' \<sigma> \<pi>"
  shows "v \<in> set \<sigma>" "v' \<in> set \<sigma>"
  using assms
  unfolding shifts_to_def
   apply (metis index_conv_size_if_notin index_le_size leD)
  by (metis assms shifts_to_def)

lemma shifts_to_inj:
  assumes "shifts_to G M u v v' \<sigma> \<pi>"
  assumes "shifts_to G M u v v'' \<sigma> \<pi>"
  shows "v' = v''"
  using assms
  unfolding shifts_to_def
  by (metis index_eq_index_conv not_less_iff_gr_or_eq)

lemma the_shifts_to:
  assumes "shifts_to G M u v v' \<sigma> \<pi>"
  shows "(THE v'. shifts_to G M u v v' \<sigma> \<pi>) = v'"
  using assms
  by (auto dest: shifts_to_inj)

lemma zig_zag_relation_unique:
  "(y,x) \<in> zig_zag_relation \<Longrightarrow> (y',x) \<in> zig_zag_relation \<Longrightarrow> y = y'"
  unfolding zig_zag_relation_def
  by (auto dest: the_match shifts_to_inj)

lemma index_gt_induct: 
  assumes "\<And>x. (\<And>y. (index xs y > index xs x \<Longrightarrow> P y)) \<Longrightarrow> P x"
  shows "P x"
  using assms
  by (induction "length xs - index xs x" arbitrary: x rule: less_induct)
     (metis diff_less_mono2 index_le_size le_less not_le)

lemma zig_zag_relation_increasing_rank:
  assumes "(Inr (G, M, u, \<sigma>, \<pi>), Inl (G, M, v, \<sigma>, \<pi>)) \<in> zig_zag_relation"
  assumes "(Inl (G, M, v', \<sigma>, \<pi>), Inr (G, M, u, \<sigma>, \<pi>)) \<in> zig_zag_relation"
  shows "index \<sigma> v < index \<sigma> v'"
proof -
  from \<open>(Inr (G, M, u, \<sigma>, \<pi>), Inl (G, M, v, \<sigma>, \<pi>)) \<in> zig_zag_relation\<close> have "matching M"
    "{u,v} \<in> M"
    unfolding zig_zag_relation_def
    by auto

  then have "(THE v. {u,v} \<in> M) = v" by (auto intro: the_match')

  with \<open>(Inl (G, M, v', \<sigma>, \<pi>), Inr (G, M, u, \<sigma>, \<pi>)) \<in> zig_zag_relation\<close> show ?thesis
    unfolding zig_zag_relation_def
    by simp
qed

lemma length_minus_index_less_index_gt:
  "length xs - index xs x < length xs - index xs x' \<longleftrightarrow> index xs x' < index xs x"
  by (induction xs) auto

lemma wf_zig_zag_relation_Inl_aux:
  assumes "\<forall>x. (\<forall>y. (y,x) \<in> zig_zag_relation \<longrightarrow> P y) \<longrightarrow> P x"
  shows "P (Inl a)"
proof (cases a)
  case (fields G M v \<sigma> \<pi>)
  have PI: "\<And>x. (\<And>y. (y,x) \<in> zig_zag_relation \<Longrightarrow> P y) \<Longrightarrow> P x" using assms by blast

  have "P (Inl (G, M, v, \<sigma>, \<pi>))"
  proof (induction "length \<sigma> - index \<sigma> v" arbitrary: v rule: less_induct)
    case less
    then show ?case
    proof (cases "\<exists>y. (y, Inl (G, M, v, \<sigma>, \<pi>)) \<in> zig_zag_relation")
      case True
      then obtain u where "(Inr (G, M, u, \<sigma>, \<pi>), Inl (G, M, v, \<sigma>, \<pi>)) \<in> zig_zag_relation"
        unfolding zig_zag_relation_def by auto

      then have "\<And>y. (y, Inl (G, M, v, \<sigma>, \<pi>)) \<in> zig_zag_relation \<Longrightarrow> y = Inr (G, M, u, \<sigma>, \<pi>)"
        by (simp add: zig_zag_relation_unique)

      show ?thesis
      proof (cases "\<exists>x'. (x', Inr (G, M, u, \<sigma>, \<pi>)) \<in> zig_zag_relation")
        case True
        then obtain v' where "(Inl (G, M, v', \<sigma>, \<pi>), Inr (G, M, u, \<sigma>, \<pi>)) \<in> zig_zag_relation"
          unfolding zig_zag_relation_def by auto

        then have "\<And>x'. (x', Inr (G, M, u, \<sigma>, \<pi>)) \<in> zig_zag_relation \<Longrightarrow> x' = Inl (G, M, v', \<sigma>, \<pi>)"
          by (simp add: zig_zag_relation_unique)

        have "P (Inl (G, M, v', \<sigma>, \<pi>))"
          using \<open>(Inr (G, M, u, \<sigma>, \<pi>), Inl (G, M, v, \<sigma>, \<pi>)) \<in> zig_zag_relation\<close>
            \<open>(Inl (G, M, v', \<sigma>, \<pi>), Inr (G, M, u, \<sigma>, \<pi>)) \<in> zig_zag_relation\<close>
          by (auto intro!: less zig_zag_relation_increasing_rank simp: length_minus_index_less_index_gt)

        then have "P (Inr (G, M, u, \<sigma>, \<pi>))"
          using PI \<open>\<And>x'. (x', Inr (G, M, u, \<sigma>, \<pi>)) \<in> zig_zag_relation \<Longrightarrow> x' = Inl (G, M, v', \<sigma>, \<pi>)\<close> by blast

        then show ?thesis
          using PI \<open>\<And>y. (y, Inl (G, M, v, \<sigma>, \<pi>)) \<in> zig_zag_relation \<Longrightarrow> y = Inr (G, M, u, \<sigma>, \<pi>)\<close> by blast
      next
        case False
        then show ?thesis
          using PI \<open>(Inr (G, M, u, \<sigma>, \<pi>), Inl (G, M, v, \<sigma>, \<pi>)) \<in> zig_zag_relation\<close> zig_zag_relation_unique by blast
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
  subgoal for M G v \<sigma> \<pi> u v'
  proof -
    assume assms: "matching M" "{u,v} \<in> M" "shifts_to G M (THE u. {u, v} \<in> M) v v' \<sigma> \<pi>"
    then have the_u: "(THE u. {u,v} \<in> M) = u" 
      by (auto intro: the_match)

    with assms have "(THE v'. shifts_to G M u v v' \<sigma> \<pi>) = v'"
      using the_shifts_to by fastforce

    with the_u show ?thesis
      by (metis assms(3) shifts_to_def)
  qed
  subgoal for M G u \<sigma> \<pi> v v'
  proof -
    assume assms: "matching M" "{u,v} \<in> M" "shifts_to G M u (THE v. {u,v} \<in> M) v' \<sigma> \<pi>"

    then have the_v: "(THE v. {u,v} \<in> M) = v"
      by (auto intro: the_match')

    with assms have "(THE v'. shifts_to G M u v v' \<sigma> \<pi>) = v'"
      using the_shifts_to by fastforce

    with assms the_v show ?thesis
      using shifts_to_def the_v by fastforce
  qed
  subgoal for M G u \<sigma> \<pi> v v'
  proof -
    assume assms: "matching M" "{u,v} \<in> M" "shifts_to G M u (THE v. {u,v} \<in> M) v' \<sigma> \<pi>"
    then have the_v: "(THE v. {u,v} \<in> M) = v" 
      by (auto intro: the_match')

    with assms have "(THE v'. shifts_to G M u v v' \<sigma> \<pi>) = v'"
      using the_shifts_to by fastforce
    with the_v assms show ?thesis
      by (simp add: shifts_to_def)
  qed
  done

thm zig_zag.induct
declare zig.simps[simp del] zag.simps[simp del]

fun_cases zig_ConsE: "zig G M v \<sigma> \<pi> = v' # uvs"
fun_cases zig_NilE: "zig G M v \<sigma> \<pi> = []"
thm zig_ConsE zig_NilE

fun_cases zag_ConsE: "zag G M u \<sigma> \<pi> = u' # uvs"
fun_cases zag_NilE: "zag G M u \<sigma> \<pi> = []"
thm zag_ConsE zag_NilE


lemma zig_matching_edge: "zig G M v \<sigma> \<pi> = v # u # uvs \<Longrightarrow> {u,v} \<in> M"
  by (auto elim!: zig_ConsE split: if_splits simp: the_match zag.simps)

lemma zag_shift_edge:
  assumes "{u,v} \<in> M"
  assumes "zag G M u \<sigma> \<pi> = u # v' # uvs"
  shows "shifts_to G M u v v' \<sigma> \<pi>"
proof -
  have the_v: "(THE v. {u,v} \<in> M) = v" 
    using assms zag_ConsE the_match' by fast

  with assms have has_shift: "\<exists>v'. shifts_to G M u v v' \<sigma> \<pi>"
    by (smt (verit, ccfv_threshold) list.inject list.simps(3) the_match' zag.simps)

  then obtain v'' where shifts_to: "shifts_to G M u v v'' \<sigma> \<pi>" by blast
  with the_shifts_to have "(THE v'. shifts_to G M u v v' \<sigma> \<pi>) = v''"
    by fastforce

  with assms the_v has_shift have "v'' = v'"
    by (auto elim: zag_ConsE split: if_splits simp: Let_def zig.simps)

  with shifts_to show ?thesis by simp
qed

lemma 
  assumes "zig G M v \<sigma> \<pi> = v # u # v' # uvs"
  shows "index \<sigma> v < index \<sigma> v'"
proof -
  have "{u,v} \<in> M" using assms zig_matching_edge by fast
  then have "(THE u. {u,v} \<in> M) = u" using assms the_match zig_ConsE by fast
  with \<open>{u,v} \<in> M\<close> assms have "zig G M v \<sigma> \<pi> = v # zag G M u \<sigma> \<pi>"
    by (auto elim!: zig_ConsE intro: the_match)

  with assms \<open>{u,v} \<in> M\<close> have "shifts_to G M u v v' \<sigma> \<pi>"
    by (auto dest: zag_shift_edge)

  then show ?thesis unfolding shifts_to_def by blast
qed

lemma step_already_matched:
  "u \<in> Vs M \<Longrightarrow> step G u \<sigma> M = M"
  by (induction \<sigma>) auto

lemma step_mono_edge:
  "{x,y} \<in> M \<Longrightarrow> {x,y} \<in> step G u \<sigma> M"
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

lemma partitioned_bipartite_subgraph:
  assumes "partitioned_bipartite G X"
  assumes "H \<subseteq> G"
  shows "partitioned_bipartite H X"
  using assms
  unfolding partitioned_bipartite_def
  apply (auto dest: Vs_subset intro: finite_subset)
  by (metis edges_are_Vs in_mono insert_commute)

lemma partitioned_bipartite_step:
  assumes "partitioned_bipartite G (set \<sigma>)"
  assumes "M \<subseteq> G"
  shows "partitioned_bipartite (step G u \<sigma> M) (set \<sigma>)"
  using assms
  by (auto dest: step_matches_graph_edge intro: partitioned_bipartite_subgraph)

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

lemma partitioned_bipartite_ranking':
  assumes "partitioned_bipartite G (set \<sigma>)"
  assumes "M \<subseteq> G"
  shows "partitioned_bipartite (ranking' G \<pi> \<sigma> M) (set \<sigma>)"
  using assms
  by (induction \<pi> arbitrary: M) 
     (auto intro: partitioned_bipartite_subgraph simp: step_matches_graph_edge)

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
     (auto dest!: edges_are_Vs)

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
  "ranking' (G \<setminus> X) \<pi> \<sigma> M = ranking' (G \<setminus> X) \<pi> (\<sigma> \<setminus> X) M"
  by (induction "G \<setminus> X" \<pi> \<sigma> M rule: ranking'.induct)
     (simp_all add: step_remove_vertices_graph_remove_vertices_rank)

lemma ranking_remove_vertices_graph_remove_vertices_rank:
  "ranking (G \<setminus> X) \<pi> \<sigma> = ranking (G \<setminus> X) \<pi> (\<sigma> \<setminus> X)"
  using ranking'_remove_vertices_graph_remove_vertices_rank
  by blast

locale wf_ranking =
  fixes G :: "'a graph"
    and \<sigma> :: "'a list"
    and \<pi> :: "'a list"
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
  assumes "shifts_to G' M u v v' \<sigma> \<pi>"
  shows "\<exists>v'. shifts_to G M u v v' \<sigma> \<pi>"
proof -
  consider (same) "shifts_to G M u v v' \<sigma> \<pi>" | (earlier) "\<not>shifts_to G M u v v' \<sigma> \<pi>" by blast
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
      proof (cases "shifts_to G M u v v'' \<sigma> \<pi>")
        case False
        have "v'' \<in> set \<sigma>" 
          using less
          by (metis index_conv_size_if_notin index_less_size_conv order.asym)

        with False less have "\<exists>v'''. index \<sigma> v < index \<sigma> v''' \<and> index \<sigma> v''' < index \<sigma> v'' \<and> {u,v'''} \<in> G \<and> (\<nexists>u'. index \<pi> u' < index \<pi> u \<and> {u',v'''} \<in> M)"
          unfolding shifts_to_def
          by (metis assms(2) shifts_to_def)
        
        with less show ?thesis by auto
      qed blast
    qed
  qed blast
qed

lemma no_shifts_to_mono:
  "G' \<subseteq> G \<Longrightarrow> \<nexists>v'. shifts_to G M u v v' \<sigma> \<pi> \<Longrightarrow> \<nexists>v'. shifts_to G' M u v v' \<sigma> \<pi>"
  by (auto dest: shifts_to_mono)

                                    
lemma remove_vertices_no_shifts_to_mono:
  "xs \<subseteq> xs' \<Longrightarrow> \<nexists>v'. shifts_to (G \<setminus> xs) M u v v' \<sigma> \<pi> \<Longrightarrow> \<nexists>u'. shifts_to (G \<setminus> xs') M u v v' \<sigma> \<pi>"
  by (auto dest: remove_vertices_mono'[of xs xs' G] no_shifts_to_mono)

lemma shifts_to_matched_vertex_higher_rank:
  assumes "shifts_to G M v u u' \<pi> \<sigma>"
  assumes "{u,v} \<in> M"
  assumes "{u',v'} \<in> M"
  assumes "matching M"
  assumes  "v \<in> set \<sigma>"
  shows "index \<sigma> v < index \<sigma> v'"
  using assms
  unfolding shifts_to_def
  apply auto
  by (smt (verit, best) index_eq_index_conv insert_commute not_less_iff_gr_or_eq the_match')

lemma remove_vertices_online_before_shifts_to:
  assumes "xs' \<subseteq> set \<sigma>"
  assumes "xs \<subseteq> xs'"
  assumes "set \<sigma> \<inter> set \<pi> = {}"
  assumes "\<forall>x \<in> xs' - xs. index \<sigma> x < index \<sigma> v"
  assumes "shifts_to (G \<setminus> xs) M v u u' \<pi> \<sigma>"
  shows "shifts_to (G \<setminus> xs') M v u u' \<pi> \<sigma>"
  using assms
  unfolding shifts_to_def
  apply (auto dest: remove_vertices_mono)
  by (smt (z3) DiffI Diff_disjoint Diff_insert_absorb disjoint_iff in_mono mem_Collect_eq nat_neq_iff remove_vertices_graph_def)

lemma remove_vertices_in_diff: "{u,v} \<in> G \<setminus> X \<Longrightarrow> {u,v} \<notin> G \<setminus> X' \<Longrightarrow> u \<in> X' - X \<or> v \<in> X' - X"
  unfolding remove_vertices_graph_def
  by simp

lemma remove_vertices_offline_shifts_to:
  assumes "xs' \<subseteq> set \<pi>"
  assumes "xs \<subseteq> xs'"
  assumes "set \<sigma> \<inter> set \<pi> = {}"
  assumes "\<forall>x \<in> xs' - xs. index \<pi> x < index \<pi> u"
  assumes "shifts_to (G \<setminus> xs) M v u u' \<pi> \<sigma>"
  shows "shifts_to (G \<setminus> xs') M v u u' \<pi> \<sigma>"
  using assms
  unfolding shifts_to_def
  apply (auto dest: remove_vertices_mono)
  by (metis disjoint_iff index_conv_size_if_notin index_le_size leD not_less_iff_gr_or_eq remove_vertices_in_diff)

lemma
  assumes "xs' \<subseteq> set \<sigma>"
  assumes "xs \<subseteq> xs'"
  assumes "set \<sigma> \<inter> set \<pi> = {}"
  shows 
   remove_vertices_online_zig_zig_eq: "(\<exists>v. {v,u} \<in> M \<Longrightarrow> \<forall>x \<in> xs' - xs. index \<sigma> x < index \<sigma> (THE v. {v,u} \<in> M)) \<Longrightarrow> zig (G \<setminus> xs) M u \<pi> \<sigma> = zig (G \<setminus> xs') M u \<pi> \<sigma>" and
   remove_vertices_online_zag_zag_eq: "(\<forall>x \<in> xs'- xs. index \<sigma> x < index \<sigma> v) \<Longrightarrow> zag (G \<setminus> xs) M v \<pi> \<sigma> = zag (G \<setminus> xs') M v \<pi> \<sigma>"
  using assms
proof (induction "G \<setminus> xs" M u \<pi> \<sigma> and "G \<setminus> xs" M v \<pi> \<sigma> rule: zig_zag.induct)
  case (1 M u \<pi> \<sigma>)                                                     
  then show ?case
  proof (cases "\<exists>v. {v,u} \<in> M")
    case True
    then obtain v where "{v,u} \<in> M" by blast
    with "1.hyps" have the_v: "(THE v. {v,u} \<in> M) = v"
      by (simp add: the_match)
    with 1 show ?thesis
      by (auto simp: zig.simps)
  next
    case False
    with 1 show ?thesis 
      by (simp add: zig.simps)
  qed
next
  case (3 M v \<pi> \<sigma>)
  consider (match) "\<exists>u. {v,u} \<in> M" | (no_match) "\<nexists>u. {v,u} \<in> M" by blast
  then show ?case
  proof cases
    case match
    then obtain u where "{v,u} \<in> M" by blast
    with "3.hyps" have the_u: "(THE u. {v,u} \<in> M) = u"
      by (simp add: the_match')

    then show ?thesis
    proof (cases "\<exists>u'. shifts_to (G \<setminus> xs) M v u u' \<pi> \<sigma>")
      case True
      then obtain u' where shift_u'_xs: "shifts_to (G \<setminus> xs) M v u u' \<pi> \<sigma>" by blast
      then have the_u'_xs: "(THE u'. shifts_to (G \<setminus> xs) M v u u' \<pi> \<sigma>) = u'"
        by (simp add: the_shifts_to)

      have shift_u'_xs': "shifts_to (G \<setminus> xs') M v u u' \<pi> \<sigma>"
        by (meson "3.prems" assms(2) remove_vertices_online_before_shifts_to shift_u'_xs)
      then have the_u'_xs': "(THE u'. shifts_to (G \<setminus> xs') M v u u' \<pi> \<sigma>) = u'" 
        by (simp add: the_shifts_to)

      have the_shifts_to_eq: "(THE u'. shifts_to (G \<setminus> xs') M v u u' \<pi> \<sigma>) = (THE u'. shifts_to (G \<setminus> xs) M v u u' \<pi> \<sigma>)"
        using the_u'_xs the_u'_xs' by blast

      have xs_before: "\<exists>v'. {v',u'} \<in> M \<Longrightarrow> \<forall>x \<in> xs' - xs. index \<sigma> x < index \<sigma> (THE v'. {v',u'} \<in> M)"
      proof
        fix x
        assume "x \<in> xs' - xs"
        assume "\<exists>v'. {v',u'} \<in> M"

        then obtain v' where "{v',u'} \<in> M" by blast
        then have the_v': "(THE v'. {v',u'} \<in> M) = v'"
          by (simp add: "3.hyps" the_match)

        have "index \<sigma> v < index \<sigma> v'"
          by (metis (no_types, lifting) "3.hyps" \<open>{v', u'} \<in> M\<close> \<open>{v, u} \<in> M\<close> antisym_conv3 index_eq_index_conv shift_u'_xs' shifts_to_def the_match')

        then show "index \<sigma> x < index \<sigma> (THE v'. {v',u'} \<in> M)"
          using "3.prems"(1) \<open>x \<in> xs' - xs\<close> dual_order.strict_trans the_v' by auto
      qed

      with 3 the_u shift_u'_xs the_u'_xs shift_u'_xs' the_u'_xs' show ?thesis
        by (auto simp: zag.simps)
        
    next
      case False
      with assms have "\<nexists>u'. shifts_to (G \<setminus> xs') M v u u' \<pi> \<sigma>"
        by (auto dest: remove_vertices_no_shifts_to_mono)

      with 3 False match the_u show ?thesis
        by (simp add: zag.simps)
    qed
  next
    case no_match
    with 3 show ?thesis 
      by (simp add: zag.simps)
  qed
qed (auto simp: zig.simps zag.simps)

lemma
  assumes "xs' \<subseteq> set \<pi>"
  assumes "xs \<subseteq> xs'"
  assumes "set \<sigma> \<inter> set \<pi> = {}"
  shows
    remove_vertices_offline_zig_zig_eq: "(\<forall>x \<in> xs' - xs. index \<pi> x < index \<pi> u) \<Longrightarrow> zig (G \<setminus> xs) M u \<pi> \<sigma> = zig (G \<setminus> xs') M u \<pi> \<sigma>" and
    remove_vertices_offline_zag_zag_eq: "(\<exists>u. {v,u} \<in> M \<Longrightarrow> \<forall>x \<in> xs' - xs. index \<pi> x < index \<pi> (THE u. {v,u} \<in> M)) \<Longrightarrow> zag (G \<setminus> xs) M v \<pi> \<sigma> = zag (G \<setminus> xs') M v \<pi> \<sigma>"
  using assms
proof (induction "G \<setminus> xs" M u \<pi> \<sigma> and "G \<setminus> xs" M v \<pi> \<sigma> rule: zig_zag.induct)
  case (1 M u \<pi> \<sigma>)
  then show ?case
  proof (cases "\<exists>v. {v,u} \<in> M")
    case True
    then obtain v where "{v,u} \<in> M" by blast
    with \<open>matching M\<close> have "(THE v. {v,u} \<in> M) = v"
      by (simp add: the_match)

    with 1 True \<open>{v,u} \<in> M\<close> the_match' show ?thesis
      by (fastforce simp: zig.simps)
  next
    case False
    with 1 show ?thesis
      by (simp add: zig.simps)
  qed
next
  case (3 M v \<pi> \<sigma>)
  consider (match) "\<exists>u. {v,u} \<in> M" | (no_match) "\<nexists>u. {v,u} \<in> M" by blast
  then show ?case 
  proof (cases)
    case match
    then obtain u where "{v,u} \<in> M" by blast
    with "3.hyps" have the_u: "(THE u. {v,u} \<in> M) = u"
      by (simp add: the_match')

    show ?thesis
    proof (cases "\<exists>u'. shifts_to (G \<setminus> xs) M v u u' \<pi> \<sigma>")
      case True
      then obtain u' where u_shifts_to_u'_xs: "shifts_to (G \<setminus> xs) M v u u' \<pi> \<sigma>" by blast
      then have the_u'_xs: "(THE u'. shifts_to (G \<setminus> xs) M v u u' \<pi> \<sigma>) = u'"
        by (simp add: the_shifts_to)

      with u_shifts_to_u'_xs "3.prems" assms have u_shifts_to_u'_xs': "shifts_to (G \<setminus> xs') M v u u' \<pi> \<sigma>"
        by (metis match remove_vertices_offline_shifts_to the_u)

      then have the_u'_xs': "(THE u'. shifts_to (G \<setminus> xs') M v u u' \<pi> \<sigma>) = u'"
        by (simp add: the_shifts_to)

      have "\<forall>x\<in>xs' - xs. index \<pi> x < index \<pi> u'"
        by (metis "3.prems"(1) match order.strict_trans shifts_to_def the_u u_shifts_to_u'_xs)

      with 3 match the_u True the_u'_xs the_u'_xs' u_shifts_to_u'_xs' show ?thesis
        by (auto simp: zag.simps)

    next
      case False

      with assms have "\<nexists>u'. shifts_to (G \<setminus> xs') M v u u' \<pi> \<sigma>"
        by (auto dest: remove_vertices_no_shifts_to_mono)

      with 3 False match the_u show ?thesis
        by (simp add: zag.simps)
    qed
  next
    case no_match
    with 3 show ?thesis
      by (simp add: zag.simps)
  qed
qed (auto simp: zig.simps zag.simps)

lemma
  assumes "{u,x} \<in> M"
  assumes "ranking_matching G M \<sigma> \<pi>"
  assumes "ranking_matching (G \<setminus> {x}) M' \<pi> \<sigma>"
  assumes "set \<sigma> \<inter> set \<pi> = {}"
  shows "zig (G \<setminus> {x}) M' u \<pi> \<sigma> = zag G M u \<sigma> \<pi>"
  using assms
proof (induction "length \<pi> - index \<pi> u" arbitrary: u x G rule: less_induct)
  case less
  let ?lhs = "zig (G \<setminus> {x}) M' u \<pi> \<sigma>"
  and ?rhs = "zag G M u \<sigma> \<pi>"

  have matching_M: "matching M" and matching_M': "matching M'" using assms
    by (auto dest: ranking_matchingD)

  from \<open>{u,x} \<in> M\<close> \<open>ranking_matching G M \<sigma> \<pi>\<close> have x_unique_match: "(THE x. {u,x} \<in> M) = x"
    by (auto dest: ranking_matchingD simp: insert_commute intro: the_match)

  from less show ?case
  proof (cases "\<exists>x'. {x',u} \<in> M'")
    case True
    then obtain x' where x'u_in_M': "{x',u} \<in> M'" by blast

    with matching_M' have unique_u_M'_match: "(THE x'. {x',u} \<in> M') = x'"
      by (auto intro: the_match)
 

    with \<open>{x',u} \<in> M'\<close> matching_M' have lhs_Cons: "?lhs = u # zag (G \<setminus> {x}) M' x' \<pi> \<sigma>"
      by (auto simp: zig.simps)
      

    from \<open>{x',u} \<in> M'\<close> matching_M' have unique_x'_M'_match: "(THE u. {x',u} \<in> M') = u"
      by (auto simp: insert_commute intro: the_match)
   

    have x_to_x': "shifts_to G M u x x' \<sigma> \<pi>"
      unfolding shifts_to_def
      sorry

    then have the_x_to_x': "(THE x'. shifts_to G M u x x' \<sigma> \<pi>) = x'"
      by (simp add: the_shifts_to)

    from x_to_x' have "x \<in> set \<sigma>" "x' \<in> set \<sigma>"
      by (meson shifts_to_only_from_input)+

    from x_to_x' the_x_to_x' x_unique_match \<open>{u,x} \<in> M\<close> matching_M have rhs_Cons: "?rhs = u # zig G M x' \<sigma> \<pi>"
      by (auto simp: zag.simps)


    show ?thesis
    proof (cases "\<exists>u'. {u',x'} \<in> M")
      case True
      then obtain u' where "{u',x'} \<in> M" by blast

      with matching_M have "(THE u'. {u',x'} \<in> M) = u'"
        by (auto intro: the_match)

      with \<open>{u',x'} \<in> M\<close> matching_M have rhs: "zig G M x' \<sigma> \<pi> = x' # zag G M u' \<sigma> \<pi>"
        by (auto simp: zig.simps)

      have u_to_u': "shifts_to (G \<setminus> {x}) M' x' u u' \<pi> \<sigma>"
        unfolding shifts_to_def sorry

      then have the_u_to_u': "(THE u'. shifts_to (G \<setminus> {x}) M' x' u u' \<pi> \<sigma>) = u'"
        by (simp add: the_shifts_to)

      with u_to_u' \<open>{x',u} \<in> M'\<close> unique_x'_M'_match matching_M' have lhs: "zag (G \<setminus> {x}) M' x' \<pi> \<sigma> = x' # zig (G \<setminus> {x}) M' u' \<pi> \<sigma>"
        by (auto simp: zag.simps)

      from u_to_u' have less_prem: "length \<pi> - index \<pi> u' < length \<pi> - index \<pi> u"
        unfolding shifts_to_def
        by (metis diff_less_mono2 dual_order.asym index_conv_size_if_notin index_less_size_conv)


      have ranking_matching_reduced: "ranking_matching (G \<setminus> {x}) M \<sigma> \<pi>"
        using ranking_matching_remove_vertices[OF \<open>ranking_matching G M \<sigma> \<pi>\<close>] by blast

      have ranking_matching_reduced': "ranking_matching (G \<setminus> {x', x}) M' \<pi> \<sigma>"
        using ranking_matching_remove_vertices[OF \<open>ranking_matching (G \<setminus> {x}) M' \<pi> \<sigma>\<close>, where X = "{x'}"]
        by (auto simp: remove_remove_union)

      have zig_zig_eq: "zig (G \<setminus> {x}) M' u' \<pi> \<sigma> = zig (G \<setminus> {x', x}) M' u' \<pi> \<sigma> "
        apply (rule remove_vertices_online_zig_zig_eq)
        using \<open>x \<in> set \<sigma>\<close> \<open>x' \<in> set \<sigma>\<close> apply blast
           apply simp
        using assms apply blast
        by (metis Diff_iff assms(3) index_eq_index_conv insert_iff not_less_iff_gr_or_eq ranking_matchingD(1) shifts_to_def the_match the_match' u_to_u' unique_x'_M'_match)

      have "index \<sigma> x < index \<sigma> x'"
        by (meson shifts_to_def x_to_x')

      have zag_zag_eq: "zag (G \<setminus> {}) M u' \<sigma> \<pi> = zag (G \<setminus> {x}) M u' \<sigma> \<pi>"
        apply (rule remove_vertices_offline_zag_zag_eq)
        using \<open>x \<in> set \<sigma>\<close> apply blast
          apply blast
        using assms apply blast
        by (metis Diff_empty \<open>index \<sigma> x < index \<sigma> x'\<close> \<open>{u', x'} \<in> M\<close> assms(2) ranking_matchingD(1) singleton_iff the_match')

      with zig_zig_eq less(1)[OF less_prem \<open>{u',x'} \<in> M\<close> ranking_matching_reduced, simplified remove_remove_union, simplified, OF ranking_matching_reduced' \<open>set \<sigma> \<inter> set \<pi> = {}\<close>]
      show ?thesis
        unfolding lhs_Cons rhs_Cons lhs rhs
        by (simp add: remove_vertices_empty)
    next
      case False

      with matching_M have rhs: "zig G M x' \<sigma> \<pi> = [x']"
        by (simp add: zig.simps)


      have "\<nexists>u'. shifts_to (G \<setminus> {x}) M' x' u u' \<pi> \<sigma>"
        unfolding shifts_to_def sorry

      with \<open>{x',u} \<in> M'\<close> unique_x'_M'_match matching_M' have lhs: "zag (G \<setminus> {x}) M' x' \<pi> \<sigma> = [x']"
        by (auto simp: zag.simps)

      with lhs_Cons rhs_Cons rhs show ?thesis by simp
    qed
  next
    case False
    with matching_M' have lhs: "zig (G \<setminus> {x}) M' u \<pi> \<sigma> = [u]"
      by (simp add: zig.simps)

    have "\<nexists>x'. shifts_to G M u x x' \<sigma> \<pi>"
    proof (rule ccontr, simp)
      assume "\<exists>x'. shifts_to G M u x x' \<sigma> \<pi>"
      then obtain x' where "shifts_to G M u x x' \<sigma> \<pi>" by blast

      with \<open>ranking_matching (G \<setminus> {x}) M' \<pi> \<sigma>\<close> have "{x',u} \<in> M'"
        unfolding ranking_matching_def shifts_to_def
        sorry

      with False show False by blast
    qed

    with x_unique_match \<open>{u,x} \<in> M\<close> matching_M have rhs: "zag G M u \<sigma> \<pi> = [u]" 
      by (auto simp: zag.simps)

    show ?thesis
      unfolding lhs rhs by (rule refl)
  qed
qed

end