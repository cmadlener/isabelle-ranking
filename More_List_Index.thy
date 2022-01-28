theory More_List_Index
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

end