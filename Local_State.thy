section \<open> Local State \<close>

theory Local_State
  imports "Variables"
begin

text \<open> This theory supports ad-hoc extension of an alphabet type with a tuple of lenses constructed
  using successive applications of @{const fst_lens} and @{const snd_lens}. It effectively allows
  local variables, since we always add a collection of new variables. \<close>

text \<open> We declare a number of syntax translations to produce lens and product types, to obtain
  a type for the overall state space, to construct a tuple that denotes the lens vector parameter, 
  to construct the vector itself, and finally to construct the state declaration. \<close>

syntax
  "_lensT" :: "type \<Rightarrow> type \<Rightarrow> type" ("LENSTYPE'(_, _')")
  "_pairT" :: "type \<Rightarrow> type \<Rightarrow> type" ("PAIRTYPE'(_, _')")
  "_state_type" :: "pttrn \<Rightarrow> type"
  "_state_tuple" :: "type \<Rightarrow> pttrn \<Rightarrow> logic"
  "_state_lenses" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("localstate (_)/ over (_)" [0, 10] 10)

translations
  (type) "PAIRTYPE('a, 'b)" => (type) "'a \<times> 'b"
  (type) "LENSTYPE('a, 'b)" => (type) "'a \<Longrightarrow> 'b"

  "_state_type (_constrain x t)" => "t"
  "_state_type (CONST Product_Type.Pair (_constrain x t) vs)" => "_pairT t (_state_type vs)"

  "_state_tuple st (_constrain x t)" => "_constrain x (_lensT t st)"
  "_state_tuple st (CONST Pair (_constrain x t) vs)" =>
    "CONST Product_Type.Pair (_constrain x (_lensT t st)) (_state_tuple st vs)"

ML \<open>

 \<close>

parse_translation \<open>
  let
    open HOLogic; open Syntax;
    fun lensT s t = Type (@{type_name lens_ext}, [s, t, HOLogic.unitT]);
    fun lens_comp a b c = Const (@{const_syntax "lens_comp"}, lensT a b --> lensT b c --> lensT a c);
    fun fst_lens t = Const (@{const_syntax "fst_lens"}, Type (@{type_name lens_ext}, [t, dummyT, unitT]));
    val snd_lens = Const (@{const_syntax "snd_lens"}, dummyT);
    fun id_lens t = Const (@{const_syntax "id_lens"},Type (@{type_name lens_ext}, [t, dummyT, unitT]));
    fun lens_syn_typ t = const @{type_syntax lens_ext} $ t $ const @{type_syntax dummy} $ const @{type_syntax unit};
    fun constrain t ty = const @{syntax_const "_constrain"} $ t $ ty;

    (* Construct a tuple of n lenses, whose source type is product of the types in ts, and each lens
       has an element of the type: prod_lens [t0, t1 ... ] 1 : t1 ==> t0 * t1 * ... *)
    fun prod_lens ts i = 
      let open Syntax; open Library; fun lens_compf (x, y) = const @{const_name lens_comp} $ x $ y in
      if (length ts = 1) 
      then Const (@{const_name id_lens}, lensT (nth ts i) (nth ts i))
      else if (length ts = i + 1) 
      then foldl lens_compf (Const (@{const_name "snd_lens"}, lensT (nth ts i) dummyT), replicate (i-1) (const @{const_name "snd_lens"}))
      else foldl lens_compf (Const (@{const_name "fst_lens"}, lensT (nth ts i) dummyT), replicate i (const @{const_name "snd_lens"}))
      end;

    (* Construct a tuple of lenses for each of the possible locally declared variables *)
    fun state_lenses ts sty st = 
      foldr1 (fn (x, y) => pair_const dummyT dummyT $ x $ y) (map (fn i => lens_comp dummyT sty dummyT $ prod_lens ts i $ st) (upto (0, length ts - 1)));

    fun
      (* Add up the number of variable declarations in the tuple *)
      var_decl_num (Const (@{const_syntax "Product_Type.Pair"},_) $ _ $ vs) = var_decl_num vs + 1 |
      var_decl_num _ = 1;

    fun
      var_decl_typs (Const (@{const_syntax "Product_Type.Pair"},_) $ (Const ("_constrain", _) $ _ $ typ) $ vs) = Syntax_Phases.decode_typ typ :: var_decl_typs vs |
      var_decl_typs (Const ("_constrain", _) $ _ $ typ) = [Syntax_Phases.decode_typ typ] |
      var_decl_typs _ = [];

    fun state_lens ctx [vs, loc] = (state_lenses (var_decl_typs vs) (mk_tupleT (var_decl_typs vs)) loc);
  in
  [("_state_lenses", state_lens)]
  end
\<close>

term "localstate (x::int, y::int) over 1\<^sub>L"

end